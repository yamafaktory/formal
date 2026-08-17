//! The HTTP surface, driven through the router rather than through a socket.
//!
//! `tests/conformance/` is the contract and judges a running server; this is the
//! same questions asked in-process, so a break shows up in `cargo test` rather
//! than only when someone remembers to point the suite at a binary.
//!
//! Nothing here checks a proof: that needs Lean, and what is being tested is the
//! routing, the refusals and the shapes.

use std::{
    sync::Arc,
    time::Duration,
};

use axum::{
    Router,
    body::Body,
    http::{
        Request,
        StatusCode,
    },
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
use http_body_util::BodyExt;
use serde_json::{
    Value,
    json,
};
use tempfile::TempDir;
use tower::ServiceExt;

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

fn app(dir: &TempDir) -> Router {
    let paths = Paths::under(dir.path().to_path_buf());
    let toolchain = Toolchain::new(
        dir.path().join("elan"),
        &std::ffi::OsString::from("/nonexistent"),
    );
    let sandbox = Sandbox::new(Mode::Off, None, &paths, &toolchain);
    let runner = Runner::new(paths, toolchain, sandbox, Duration::from_secs(5));
    let state = AppState::new(
        Sessions::default(),
        ProofCache::new(dir.path().join("cache"), Duration::from_hours(24 * 7)),
        runner,
    )
    .expect("the shipped hint table is valid");
    router(Arc::new(state))
}

async fn call(app: &Router, method: &str, path: &str, body: Option<Value>) -> (StatusCode, Value) {
    let request = Request::builder().method(method).uri(path);
    let request = match body {
        Some(body) => request
            .header("content-type", "application/json")
            .body(Body::from(body.to_string())),
        None => request.body(Body::empty()),
    }
    .expect("the request is well formed");

    let response = app
        .clone()
        .oneshot(request)
        .await
        .expect("the router answers");
    let status = response.status();
    let bytes = response
        .into_body()
        .collect()
        .await
        .expect("the body is readable")
        .to_bytes();
    let value = serde_json::from_slice(&bytes).unwrap_or(Value::Null);
    (status, value)
}

/// Open a session over the two properties and hand back its id.
async fn open(app: &Router) -> String {
    let (status, body) = call(
        app,
        "POST",
        "/session",
        Some(json!({ "properties": properties() })),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{body}");
    body["session_id"].as_str().expect("an id").to_string()
}

mod unauthenticated_reads {
    use super::*;

    #[tokio::test]
    async fn health_is_ok() {
        let dir = TempDir::new().expect("a temporary directory");
        let (status, body) = call(&app(&dir), "GET", "/health", None).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(body, json!({ "status": "ok" }));
    }

    #[tokio::test]
    async fn the_guide_index_names_its_topics() {
        let dir = TempDir::new().expect("a temporary directory");
        let (status, body) = call(&app(&dir), "GET", "/guide", None).await;
        assert_eq!(status, StatusCode::OK);
        for topic in ["extract", "formalize", "tactics"] {
            assert!(body["topics"][topic].is_string(), "{topic}");
        }
        assert!(
            body["workflow"]
                .as_array()
                .is_some_and(|steps| !steps.is_empty())
        );
    }

    #[tokio::test]
    async fn every_topic_is_servable() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        for topic in ["extract", "formalize", "tactics"] {
            let (status, body) = call(&app, "GET", &format!("/guide/{topic}"), None).await;
            assert_eq!(status, StatusCode::OK, "{topic}");
            assert_eq!(body["topic"], topic);
            assert!(
                body["instructions"]
                    .as_str()
                    .is_some_and(|text| text.len() > 400)
            );
        }
    }

    #[tokio::test]
    async fn a_topic_that_does_not_exist_names_the_ones_that_do() {
        let dir = TempDir::new().expect("a temporary directory");
        let (status, body) = call(&app(&dir), "GET", "/guide/no-such-topic", None).await;
        assert_eq!(status, StatusCode::NOT_FOUND);
        assert_eq!(
            body["detail"],
            "No such topic: no-such-topic. Try: extract, formalize, tactics"
        );
    }
}

mod schema {
    use super::*;

    #[tokio::test]
    async fn openapi_documents_every_route_the_router_serves() {
        let dir = TempDir::new().expect("a temporary directory");
        let (status, doc) = call(&app(&dir), "GET", "/openapi.json", None).await;
        assert_eq!(status, StatusCode::OK);

        let paths = doc["paths"].as_object().expect("an object");
        for (path, method) in [
            ("/health", "get"),
            ("/guide", "get"),
            ("/guide/{topic}", "get"),
            ("/session", "post"),
            ("/session/{session_id}", "get"),
            ("/session/{session_id}", "delete"),
            ("/session/{session_id}/check", "post"),
            ("/session/{session_id}/proof/{property_id}", "get"),
        ] {
            assert!(paths[path][method].is_object(), "{method} {path}");
        }
    }

    #[tokio::test]
    async fn the_shape_of_a_refusal_is_documented_too() {
        let dir = TempDir::new().expect("a temporary directory");
        let (_, doc) = call(&app(&dir), "GET", "/openapi.json", None).await;
        assert!(doc["components"]["schemas"]["Detail"].is_object(), "{doc}");
        assert_eq!(
            doc["paths"]["/session"]["post"]["responses"]["400"]["content"]["application/json"]["schema"]
                ["$ref"],
            "#/components/schemas/Detail"
        );
    }

    #[tokio::test]
    async fn every_wire_type_is_in_the_schema() {
        let dir = TempDir::new().expect("a temporary directory");
        let (_, doc) = call(&app(&dir), "GET", "/openapi.json", None).await;
        let schemas = doc["components"]["schemas"].as_object().expect("an object");
        for name in [
            "CacheHitOut",
            "CheckRequest",
            "CheckResponse",
            "Detail",
            "FailureOut",
            "ProofOut",
            "PropertySpecIn",
            "SessionRequest",
            "SessionResponse",
        ] {
            assert!(schemas.contains_key(name), "{name}");
        }
    }

    #[tokio::test]
    async fn the_version_is_the_one_the_crate_was_built_with() {
        let dir = TempDir::new().expect("a temporary directory");
        let (_, doc) = call(&app(&dir), "GET", "/openapi.json", None).await;
        assert_eq!(doc["info"]["title"], "formal");
        assert_eq!(doc["info"]["version"], env!("CARGO_PKG_VERSION"));
    }
}

mod opening_a_session {
    use super::*;

    #[tokio::test]
    async fn properties_become_work() {
        let dir = TempDir::new().expect("a temporary directory");
        let (status, body) = call(
            &app(&dir),
            "POST",
            "/session",
            Some(json!({ "properties": properties() })),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(
            body["work"],
            json!(["reverse/involutive", "reverse/length"])
        );
        assert_eq!(body["cached"], json!([]));
        assert_eq!(body["stale"], json!([]));
        assert_eq!(body["complete"], json!(false));
    }

    #[tokio::test]
    async fn neither_and_both_are_refused_the_same_way() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        for body in [
            json!({}),
            json!({ "properties": properties(), "spec_file": "/tmp/x.json" }),
        ] {
            let (status, answer) = call(&app, "POST", "/session", Some(body)).await;
            assert_eq!(status, StatusCode::BAD_REQUEST);
            assert_eq!(
                answer["detail"],
                "Provide either 'properties' or 'spec_file', not both"
            );
        }
    }

    #[tokio::test]
    async fn two_properties_under_one_id_are_refused() {
        let dir = TempDir::new().expect("a temporary directory");
        let one = properties()[0].clone();
        let (status, body) = call(
            &app(&dir),
            "POST",
            "/session",
            Some(json!({ "properties": [one.clone(), one] })),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
        assert_eq!(body["detail"], "Duplicate property ids: reverse/involutive");
    }

    #[tokio::test]
    async fn a_relative_spec_file_is_refused() {
        let dir = TempDir::new().expect("a temporary directory");
        let (status, body) = call(
            &app(&dir),
            "POST",
            "/session",
            Some(json!({ "spec_file": "relative.properties.json" })),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
        assert!(
            body["detail"]
                .as_str()
                .is_some_and(|d| d.starts_with("spec file path must be absolute")),
            "{body}"
        );
    }

    #[tokio::test]
    async fn a_spec_file_is_read_and_its_stale_properties_reported() {
        let dir = TempDir::new().expect("a temporary directory");
        std::fs::write(dir.path().join("source.py"), "def identity(x): return x\n")
            .expect("writable");
        let spec = dir.path().join("conformance.properties.json");
        std::fs::write(
            &spec,
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
            .to_string(),
        )
        .expect("writable");

        let (status, body) = call(
            &app(&dir),
            "POST",
            "/session",
            Some(json!({ "spec_file": spec.to_string_lossy() })),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{body}");
        assert_eq!(body["work"], json!(["identity/fixed"]));
        assert_eq!(body["stale"], json!(["gone/stale"]));
    }
}

mod reading_and_closing {
    use super::*;

    #[tokio::test]
    async fn a_session_reads_back_as_it_was_opened() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        let id = open(&app).await;
        let (status, body) = call(&app, "GET", &format!("/session/{id}"), None).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(body["session_id"], id);
        assert_eq!(
            body["work"],
            json!(["reverse/involutive", "reverse/length"])
        );
    }

    #[tokio::test]
    async fn a_session_nobody_opened_is_not_found_everywhere() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        let expected = format!("No such session: {UNKNOWN_SESSION}");
        for (method, path, body) in [
            ("GET", format!("/session/{UNKNOWN_SESSION}"), None),
            (
                "POST",
                format!("/session/{UNKNOWN_SESSION}/check"),
                Some(json!({ "proofs": { "a": "b" } })),
            ),
            (
                "GET",
                format!("/session/{UNKNOWN_SESSION}/proof/reverse/involutive"),
                None,
            ),
            ("DELETE", format!("/session/{UNKNOWN_SESSION}"), None),
        ] {
            let (status, answer) = call(&app, method, &path, body).await;
            assert_eq!(status, StatusCode::NOT_FOUND, "{method} {path}");
            assert_eq!(answer["detail"], expected, "{method} {path}");
        }
    }

    #[tokio::test]
    async fn closing_twice_is_honest_about_the_second_time() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        let id = open(&app).await;

        let (status, body) = call(&app, "DELETE", &format!("/session/{id}"), None).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(body, json!({ "status": "closed" }));

        let (status, body) = call(&app, "DELETE", &format!("/session/{id}"), None).await;
        assert_eq!(status, StatusCode::NOT_FOUND);
        assert_eq!(body["detail"], format!("No such session: {id}"));

        let (status, _) = call(&app, "GET", &format!("/session/{id}"), None).await;
        assert_eq!(status, StatusCode::NOT_FOUND);
    }
}

mod checking {
    use super::*;

    #[tokio::test]
    async fn neither_and_both_are_refused_the_same_way() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        let id = open(&app).await;
        let path = format!("/session/{id}/check");
        for body in [
            json!({}),
            json!({ "proofs": { "reverse/involutive": "x" }, "proof_files": { "a": "/b.lean" } }),
        ] {
            let (status, answer) = call(&app, "POST", &path, Some(body)).await;
            assert_eq!(status, StatusCode::BAD_REQUEST);
            assert_eq!(
                answer["detail"],
                "Provide either 'proofs' or 'proof_files', not both"
            );
        }
    }

    #[tokio::test]
    async fn an_unregistered_id_is_refused_before_lean_is_paid_for() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        let id = open(&app).await;
        let (status, body) = call(
            &app,
            "POST",
            &format!("/session/{id}/check"),
            Some(json!({ "proofs": { "not/registered": "theorem t : True := trivial" } })),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
        assert_eq!(
            body["detail"],
            "Not registered in this session: not/registered"
        );
    }

    #[tokio::test]
    async fn a_relative_proof_file_is_refused_by_the_id_it_was_sent_for() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        let id = open(&app).await;
        let (status, body) = call(
            &app,
            "POST",
            &format!("/session/{id}/check"),
            Some(json!({ "proof_files": { "reverse/involutive": "proof.lean" } })),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
        assert!(
            body["detail"].as_str().is_some_and(
                |d| d.starts_with("proof file for reverse/involutive path must be absolute")
            ),
            "{body}"
        );
    }
}

mod fetching_a_proof {
    use super::*;

    #[tokio::test]
    async fn an_id_with_a_slash_in_it_still_reaches_the_endpoint() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        let id = open(&app).await;
        let (status, body) = call(
            &app,
            "GET",
            &format!("/session/{id}/proof/reverse/involutive"),
            None,
        )
        .await;
        assert_eq!(
            status,
            StatusCode::NOT_FOUND,
            "registered but unproved, which is a different 404 from unroutable"
        );
        assert_eq!(
            body["detail"],
            "Nothing accepted yet for reverse/involutive"
        );
    }

    #[tokio::test]
    async fn an_id_the_session_never_registered_says_so() {
        let dir = TempDir::new().expect("a temporary directory");
        let app = app(&dir);
        let id = open(&app).await;
        let (status, body) = call(
            &app,
            "GET",
            &format!("/session/{id}/proof/not/registered"),
            None,
        )
        .await;
        assert_eq!(status, StatusCode::NOT_FOUND);
        assert_eq!(
            body["detail"],
            "Not registered in this session: not/registered"
        );
    }
}
