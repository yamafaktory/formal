//! What formal's HTTP surface must do, driven over a real socket.
//!
//! `golden/responses.json` says what each request must be answered with. This
//! drives a server through the whole surface and compares. The golden file is the
//! contract; this is one way of asking the questions.
//!
//! Two rules about what gets pinned, kept from the suite this replaces. Status
//! codes are pinned everywhere, including on the paths that only exist to be
//! refused — half of an API is what it rejects. Bodies are pinned where formal
//! writes them and left alone where the framework does: a 422 body is axum's
//! shape, not formal's contract, so the code is checked and that is all.
//!
//! Long strings are recorded as a digest. The guidance texts are version
//! controlled next to the server that serves them, so a diff there is already
//! reviewable, and 30KB of prose inside the golden file would make every other
//! line of it unreadable.
//!
//! Set `FORMAL_CONFORMANCE_URL` to judge an already-running server instead of the
//! one these tests start.

use std::{
    collections::BTreeMap,
    fs,
    path::{
        Path,
        PathBuf,
    },
    time::Duration,
};

use formal_lean::{
    paths::Paths,
    run::Runner,
    sandbox::{
        Mode,
        Sandbox,
    },
    toolchain::Toolchain,
};
use formal_server::{
    AppState,
    router,
};
use formal_service::{
    cache::ProofCache,
    session::Sessions,
};
use serde_json::{
    Value,
    json,
};
use sha2::{
    Digest,
    Sha256,
};
use tempfile::TempDir;
use tokio::{
    io::{
        AsyncReadExt,
        AsyncWriteExt,
    },
    net::TcpStream,
};

/// The length above which a string is recorded as a digest.
const DIGEST_OVER: usize = 400;

/// A session id that no server will ever hand out.
const UNKNOWN_SESSION: &str = "0000000000000000";

fn properties() -> Value {
    json!([
        {
            "id": "reverse/involutive",
            "description": "reversing twice returns the original list",
            "kind": "invariant",
            "function": "reverse",
            "function_code": "def reverse(xs): return xs[::-1]",
            "formal": "forall xs, reverse (reverse xs) = xs",
            "preconditions": [],
            "assumptions": [],
        },
        {
            "id": "reverse/length",
            "description": "reversing preserves length",
            "kind": "invariant",
            "function": "reverse",
            "function_code": "def reverse(xs): return xs[::-1]",
            "formal": "forall xs, (reverse xs).length = xs.length",
            "preconditions": [],
            "assumptions": [],
        }
    ])
}

fn spec_file() -> Value {
    json!({
        "version": 1,
        "properties": [
            {
                "id": "identity/fixed",
                "description": "the identity function returns its argument",
                "kind": "invariant",
                "function": "identity",
                "function_code": "def identity(x): return x",
                "source_file": "source.py",
                "formal": "forall x, identity x = x",
            },
            {
                "id": "gone/stale",
                "description": "written against source that has since changed",
                "kind": "invariant",
                "function": "gone",
                "function_code": "def gone(x): return x + 1",
                "source_file": "source.py",
                "formal": "forall x, gone x > x",
            }
        ],
    })
}

/// The source the spec file is written against, and no longer describes.
const SOURCE_FILE: &str = "def identity(x): return x\n";

fn digest(text: &str) -> Value {
    json!({
        "sha256": format!("{:x}", Sha256::digest(text.as_bytes())),
        "chars": text.chars().count(),
    })
}

/// Strip out what legitimately differs between two runs of the same server.
fn normalise(value: &Value, replacements: &BTreeMap<String, String>) -> Value {
    match value {
        Value::String(text) => {
            let mut text = text.clone();
            for (original, placeholder) in replacements {
                text = text.replace(original, placeholder);
            }
            if text.chars().count() > DIGEST_OVER {
                digest(&text)
            } else {
                Value::String(text)
            }
        }
        Value::Array(items) => Value::Array(
            items
                .iter()
                .map(|item| normalise(item, replacements))
                .collect(),
        ),
        Value::Object(fields) => Value::Object(
            fields
                .iter()
                .map(|(name, field)| (name.clone(), normalise(field, replacements)))
                .collect(),
        ),
        Value::Null | Value::Bool(_) | Value::Number(_) => value.clone(),
    }
}

/// One request over a socket, answered as a status and a body.
///
/// A hand-written client rather than a dependency: three verbs, one host, one
/// fixed shape, and `Connection: close` means the body is whatever arrives before
/// the end of the stream.
async fn request(base_url: &str, method: &str, path: &str, body: Option<&Value>) -> (u16, Value) {
    let address = base_url.trim_start_matches("http://");
    let mut stream = TcpStream::connect(address)
        .await
        .expect("the server is listening");

    let payload = body.map(std::string::ToString::to_string);
    let mut head = format!("{method} {path} HTTP/1.1\r\nHost: {address}\r\nConnection: close\r\n");
    if let Some(payload) = &payload {
        use std::fmt::Write;
        head.push_str("Content-Type: application/json\r\n");
        let _ = writeln!(head, "Content-Length: {}\r", payload.len());
    }
    head.push_str("\r\n");
    stream
        .write_all(head.as_bytes())
        .await
        .expect("the request is sent");
    if let Some(payload) = &payload {
        stream
            .write_all(payload.as_bytes())
            .await
            .expect("the body is sent");
    }
    stream.flush().await.expect("the request is flushed");

    let mut response = Vec::new();
    stream
        .read_to_end(&mut response)
        .await
        .expect("the answer arrives");
    let response = String::from_utf8_lossy(&response);

    let status = response
        .split_whitespace()
        .nth(1)
        .and_then(|code| code.parse().ok())
        .unwrap_or(0);
    let payload = response
        .split_once("\r\n\r\n")
        .map_or("", |(_, body)| body)
        .trim_end_matches('\0');
    (status, serde_json::from_str(payload).unwrap_or(Value::Null))
}

/// Everything one run of the suite accumulates.
struct Run {
    base_url: String,
    workspace: PathBuf,
    recorded: BTreeMap<String, Value>,
    replacements: BTreeMap<String, String>,
}

impl Run {
    async fn step(&mut self, name: &str, method: &str, path: &str, body: Option<Value>) -> Value {
        let (status, payload) = request(&self.base_url, method, path, body.as_ref()).await;
        let mut entry = json!({ "status": status });
        if status != 422 {
            entry["body"] = normalise(&payload, &self.replacements);
        }
        self.recorded.insert(name.to_string(), entry);
        payload
    }

    /// Register the id as a placeholder before recording, since it is in the body.
    async fn open_session(&mut self, name: &str, body: Value, placeholder: &str) -> String {
        let (status, payload) = request(&self.base_url, "POST", "/session", Some(&body)).await;
        let session_id = payload["session_id"]
            .as_str()
            .unwrap_or_default()
            .to_string();
        if !session_id.is_empty() {
            self.replacements
                .insert(session_id.clone(), placeholder.to_string());
        }
        self.recorded.insert(
            name.to_string(),
            json!({ "status": status, "body": normalise(&payload, &self.replacements) }),
        );
        session_id
    }

    /// Everything that can be asked without a session.
    async fn guide(&mut self) {
        self.step("health", "GET", "/health", None).await;
        self.step("guide_index", "GET", "/guide", None).await;
        for topic in ["extract", "formalize", "tactics"] {
            self.step(
                &format!("guide_{topic}"),
                "GET",
                &format!("/guide/{topic}"),
                None,
            )
            .await;
        }
        self.step("guide_unknown_topic", "GET", "/guide/no-such-topic", None)
            .await;
    }

    /// Opening one, reading it back, and every way of opening one wrongly.
    async fn sessions(&mut self, spec_path: &str, missing_path: &str) -> (String, String) {
        let session = self
            .open_session(
                "session_open",
                json!({ "properties": properties() }),
                "<session>",
            )
            .await;

        self.step("session_read", "GET", &format!("/session/{session}"), None)
            .await;
        self.step(
            "session_read_unknown",
            "GET",
            &format!("/session/{UNKNOWN_SESSION}"),
            None,
        )
        .await;

        self.step(
            "session_open_with_neither",
            "POST",
            "/session",
            Some(json!({})),
        )
        .await;
        self.step(
            "session_open_with_both",
            "POST",
            "/session",
            Some(json!({ "properties": properties(), "spec_file": spec_path })),
        )
        .await;
        self.step(
            "session_open_duplicate_ids",
            "POST",
            "/session",
            Some(json!({ "properties": [properties()[0], properties()[0]] })),
        )
        .await;
        self.step(
            "session_open_relative_spec",
            "POST",
            "/session",
            Some(json!({ "spec_file": "relative.properties.json" })),
        )
        .await;
        self.step(
            "session_open_absent_spec",
            "POST",
            "/session",
            Some(json!({ "spec_file": missing_path })),
        )
        .await;

        let spec_session = self
            .open_session(
                "session_open_from_spec",
                json!({ "spec_file": spec_path }),
                "<spec-session>",
            )
            .await;
        (session, spec_session)
    }

    /// Every way of submitting a proof that does not reach Lean.
    async fn checks(&mut self, session: &str) {
        let check = format!("/session/{session}/check");
        self.step("check_with_neither", "POST", &check, Some(json!({})))
            .await;
        self.step(
            "check_with_both",
            "POST",
            &check,
            Some(json!({ "proofs": { "reverse/involutive": "x" }, "proof_files": { "a": "/b.lean" } })),
        )
        .await;
        self.step(
            "check_unknown_property",
            "POST",
            &check,
            Some(json!({ "proofs": { "not/registered": "theorem t : True := trivial" } })),
        )
        .await;
        self.step(
            "check_relative_proof_file",
            "POST",
            &check,
            Some(json!({ "proof_files": { "reverse/involutive": "proof.lean" } })),
        )
        .await;
        self.step(
            "check_on_unknown_session",
            "POST",
            &format!("/session/{UNKNOWN_SESSION}/check"),
            Some(json!({ "proofs": { "a": "b" } })),
        )
        .await;
    }

    /// Asking for a proof, in each of the ways there is not one.
    async fn proofs(&mut self, session: &str) {
        self.step(
            "proof_unregistered",
            "GET",
            &format!("/session/{session}/proof/not/registered"),
            None,
        )
        .await;
        self.step(
            "proof_not_yet_accepted",
            "GET",
            &format!("/session/{session}/proof/reverse/involutive"),
            None,
        )
        .await;
        self.step(
            "proof_on_unknown_session",
            "GET",
            &format!("/session/{UNKNOWN_SESSION}/proof/reverse/involutive"),
            None,
        )
        .await;
    }

    /// Closing what was opened, twice, and reading it afterwards.
    async fn closing(&mut self, session: &str, spec_session: &str) {
        self.step(
            "session_close",
            "DELETE",
            &format!("/session/{session}"),
            None,
        )
        .await;
        self.step(
            "session_close_again",
            "DELETE",
            &format!("/session/{session}"),
            None,
        )
        .await;
        self.step(
            "session_read_after_close",
            "GET",
            &format!("/session/{session}"),
            None,
        )
        .await;
        self.step(
            "session_close_spec_session",
            "DELETE",
            &format!("/session/{spec_session}"),
            None,
        )
        .await;
    }

    /// Drive one server through the whole surface and return what it answered.
    async fn all(&mut self) {
        let spec_path = self.workspace.join("conformance.properties.json");
        fs::write(self.workspace.join("source.py"), SOURCE_FILE).expect("writable");
        fs::write(&spec_path, spec_file().to_string()).expect("writable");
        let spec_path = spec_path.to_string_lossy().to_string();
        let missing_path = self
            .workspace
            .join("absent.properties.json")
            .to_string_lossy()
            .to_string();
        self.replacements.insert(
            self.workspace.to_string_lossy().to_string(),
            "<workspace>".to_string(),
        );

        self.guide().await;
        let (session, spec_session) = self.sessions(&spec_path, &missing_path).await;
        self.checks(&session).await;
        self.proofs(&session).await;
        self.closing(&session, &spec_session).await;
    }
}

fn golden() -> BTreeMap<String, Value> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/conformance/golden/responses.json");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{} — {e}", path.display()));
    serde_json::from_str(&text).expect("the golden file is JSON")
}

/// Every disagreement, by step — a port wants the whole list, not the first one.
fn differences(
    recorded: &BTreeMap<String, Value>,
    golden: &BTreeMap<String, Value>,
) -> Vec<String> {
    let mut problems = Vec::new();
    for name in golden.keys().filter(|name| !recorded.contains_key(*name)) {
        problems.push(format!("{name}: not exercised"));
    }
    for name in recorded.keys().filter(|name| !golden.contains_key(*name)) {
        problems.push(format!("{name}: not in the golden file"));
    }
    for (name, got) in recorded {
        let Some(want) = golden.get(name) else {
            continue;
        };
        if got["status"] != want["status"] {
            problems.push(format!(
                "{name}: status {}, expected {}",
                got["status"], want["status"]
            ));
        }
        if got.get("body") != want.get("body") {
            problems.push(format!(
                "{name}: body\n     got {}\n    want {}",
                got.get("body").unwrap_or(&Value::Null),
                want.get("body").unwrap_or(&Value::Null)
            ));
        }
    }
    problems
}

/// A server on a real port, and somewhere for the suite to put its files.
async fn serving(workspace: &TempDir) -> (String, tokio::task::JoinHandle<()>) {
    let home = workspace.path().join("home");
    let paths = Paths::under(home);
    let toolchain = Toolchain::new(
        workspace.path().join("elan"),
        &std::ffi::OsString::from("/nonexistent"),
    );
    let sandbox = Sandbox::new(Mode::Off, None, &paths, &toolchain);
    let cache = ProofCache::new(paths.proof_cache_dir.clone(), Duration::from_hours(24 * 7));
    let runner = Runner::new(paths, toolchain, sandbox, Duration::from_secs(5));
    let state = std::sync::Arc::new(
        AppState::new(Sessions::default(), cache, runner).expect("the shipped hint table is valid"),
    );

    let listener = tokio::net::TcpListener::bind("127.0.0.1:0")
        .await
        .expect("a port is free");
    let address = listener.local_addr().expect("it is bound");
    let served = tokio::spawn(async move {
        let _ = axum::serve(listener, router(state)).await;
    });
    (format!("http://{address}"), served)
}

#[tokio::test]
async fn the_http_surface_still_answers_what_was_recorded() {
    let workspace = TempDir::new().expect("a temporary directory");
    let external = std::env::var("FORMAL_CONFORMANCE_URL").ok();
    let (base_url, served) = match &external {
        Some(url) => (url.clone(), tokio::spawn(async {})),
        None => serving(&workspace).await,
    };

    let mut run = Run {
        base_url,
        workspace: workspace.path().to_path_buf(),
        recorded: BTreeMap::new(),
        replacements: BTreeMap::new(),
    };
    run.all().await;
    served.abort();

    let golden = golden();
    let problems = differences(&run.recorded, &golden);
    assert!(
        problems.is_empty(),
        "{}/{} steps conformant\n\n{}",
        golden.len() - problems.len(),
        golden.len(),
        problems.join("\n")
    );
    assert_eq!(
        run.recorded.len(),
        27,
        "every step the golden file records was exercised"
    );
}

#[test]
fn the_digest_rule_is_the_one_the_golden_file_was_recorded_under() {
    let short = Value::String("a".repeat(DIGEST_OVER));
    assert_eq!(normalise(&short, &BTreeMap::new()), short);
    let long = Value::String("a".repeat(DIGEST_OVER + 1));
    assert_eq!(normalise(&long, &BTreeMap::new())["chars"], DIGEST_OVER + 1);
}

#[test]
fn what_differs_between_two_runs_is_replaced_before_it_is_digested() {
    let replacements = BTreeMap::from([("abc123".to_string(), "<session>".to_string())]);
    let value = Value::String("session abc123 opened".to_string());
    assert_eq!(
        normalise(&value, &replacements),
        json!("session <session> opened")
    );
}

#[test]
fn a_missing_step_and_an_unexpected_one_are_both_reported() {
    let recorded = BTreeMap::from([("extra".to_string(), json!({ "status": 200 }))]);
    let golden = BTreeMap::from([("absent".to_string(), json!({ "status": 200 }))]);
    let problems = differences(&recorded, &golden);
    assert!(
        problems.iter().any(|p| p.contains("absent: not exercised")),
        "{problems:?}"
    );
    assert!(
        problems
            .iter()
            .any(|p| p.contains("extra: not in the golden file")),
        "{problems:?}"
    );
}

#[test]
fn the_golden_file_still_names_the_whole_surface() {
    assert_eq!(golden().len(), 27);
}

/// The golden file lives outside the crate, so nothing rebuilds when it changes.
#[test]
fn the_golden_file_is_where_it_is_expected() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/conformance/golden/responses.json");
    assert!(Path::new(&path).is_file(), "{}", path.display());
}
