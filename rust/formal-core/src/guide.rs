//! What formal knows about writing properties, served to whoever is driving it.
//!
//! Served in stages because it is not small: the index is the workflow and the
//! spec schema, and each phase's instructions are fetched only when that phase
//! starts. Handing an agent four thousand tokens of Lean conventions before it
//! has decided what to prove is the kind of waste this whole design exists to
//! remove.

use serde_json::{
    Value,
    json,
};

use crate::prompts;

/// What a `{field}` in the guidance stands for once it is served rather than sent
/// to a model.
const PLACEHOLDERS: &[(&str, &str)] = &[
    ("language", "<the source language, e.g. Python>"),
    ("code", "<the full source of the file under test>"),
    ("feature_summary", "<one sentence on what the file does>"),
    (
        "pure_functions",
        "<the pure functions you identified, with their source>",
    ),
    (
        "function_code",
        "<the source of the function this property is about>",
    ),
    ("description", "<the property's description field>"),
    ("formal", "<the property's formal field>"),
    ("kind", "<the property's kind field>"),
    (
        "preconditions",
        "<the property's preconditions, one per line>",
    ),
    ("assumptions", "<the property's assumptions, one per line>"),
    ("error", "<the error field from the failed check>"),
    ("line", "<the line field>"),
    ("col", "<the col field>"),
    ("hint", "<the hint field>"),
    ("current", "<the proof Lean rejected>"),
];

/// The categories a property can be, and what each one claims.
const KINDS: &[(&str, &str)] = &[
    (
        "bound",
        "a value is constrained — non-negative, within a range, never empty",
    ),
    (
        "identity",
        "two expressions are equal, or one rewrites to the other",
    ),
    (
        "monotonicity",
        "ordering is preserved: larger input, no smaller output",
    ),
    (
        "commutativity",
        "order of arguments or operations does not matter",
    ),
    ("idempotency", "applying twice is the same as applying once"),
    (
        "invariant",
        "something is preserved or always holds — a count, a well-formedness",
    ),
    (
        "counterexample",
        "two concrete inputs that must differ and do not, or must agree and do not — a proven defect rather than a \
         reassurance",
    ),
];

/// The topics, their one-line summaries, and the order the index lists them in.
const TOPICS: &[(&str, &str)] = &[
    (
        "extract",
        "how to identify pure functions and the properties worth proving",
    ),
    (
        "formalize",
        "Lean 4 conventions for stating and proving a property",
    ),
    (
        "tactics",
        "tactic rules that prevent the common failures, and what to do when Lean rejects a proof",
    ),
];

const WORKFLOW: &[&str] = &[
    "Read the source file you intend to check.",
    "GET /guide/extract, and GET /guide/formalize and /guide/tactics too before you commit to anything: what is \
     practically provable in Lean is what decides which properties belong in the spec file, and the spec file is the \
     thing you commit.",
    "Identify the pure functions and the properties worth proving about them.",
    "Write those properties to a spec file (see spec_file below), adding source_file and function_code to each. Commit \
     it: it is reviewable, and identical bytes each run are what let the proof cache work at all.",
    "If a spec file already exists, use it as it stands rather than regenerating it — its ids and wordings are what \
     the cached proofs are keyed on, and rewriting them throws every hit away. Add to it; do not replace it.",
    "POST /session with {'spec_file': '<absolute path>'}. The reply says which properties are already cached, which \
     need proving, and which are stale. The path must be absolute: the server resolves it, and its working directory \
     is not yours.",
    "GET /guide/formalize, then write a Lean 4 theorem and proof for each id under 'work' — that field is a list of \
     bare id strings, while 'cached' is a list of objects. GET /guide/tactics too — most first-attempt failures are \
     one of the rules it lists.",
    "POST /session/{session_id}/check with {'proof_files': {'<id>': '<absolute path to .lean>'}} — the server reads \
     them, so you do not have to load and escape each file into JSON. {'proofs': {'<id>': '<lean>'}} still works when \
     the proof is not on the server's disk.",
    "For each failure, read its error and hint, fix that proof, and resubmit only the ids that failed — the first \
     submission carries everything, a retry carries only what broke. Repeat until 'complete' is true.",
];

const SESSION_LIFETIME: &str = "A session is in-memory and expires after an idle period (SESSION_TTL_MINUTES, one hour by default), and it is \
     lost if the server restarts. Once it is gone, POST /session again with the same spec file: anything already \
     proved comes straight back as a cache hit, so you never reprove it. A 404 from /session/{id}/check means \
     expired, not wrong — reopen and carry on.";

const WHAT_VERIFIED_MEANS: &str = "A verified id means Lean accepted a proof of that theorem — not necessarily the proof you sent. Before reporting \
     a failure, formal retries the goal with a fixed tactic chain and then searches Mathlib for a lemma that closes \
     it, so a proof of yours that did not work may still come back verified because something else did. The check \
     response lists those ids under 'recovered', and GET /session/{id}/proof/{property_id} returns it as the \
     `lean_code` field, with its origin: submitted, recovered, or cache. The accepted proof is the one that was \
     cached, so it is the artefact of record — read it before reporting that your proof worked.";

const STALE_ADVICE: &str = "A stale id means the function changed since the property was written against it, so the property may no longer \
     describe anything. Re-read that function, rewrite the property, and update its function_code in the spec file. \
     Stale properties are never proved.";

const OPENAPI: &str = "GET /openapi.json is the full schema of every endpoint and response, including field types. \
                       Read it rather than guessing at a shape.";

const SPEC_FILE_STEP: &str = "Write the properties you judged verifiable into the spec file described by GET /guide, one entry each, with \
     source_file and function_code filled in. Choose ids you would choose again next run: they are the diff a human \
     reads, and the spec file is the thing you commit.";

const CONTIGUOUS_SLICE: &str = "function_code must be a contiguous slice of source_file, copied verbatim. Staleness is checked by looking for \
     that text in the current file, compared with trailing whitespace ignored — so reindenting the file is not a \
     change, but editing the function is, and the property is then reported stale rather than proved. Include \
     anything the property actually depends on: if it is about a lookup table the function reads, put the table in \
     the slice too, so editing the table invalidates the property.";

const AFTER_A_REJECTION: &str = "The check response gives you the first error, its position, and a hint chosen for that specific error. Fix that \
     one and resubmit only the ids that failed — a proof already accepted is never re-checked.";

const SUBMITTING: &str = "Point the check endpoint at your .lean files with `proof_files` and let the server read them; pass `proofs` \
     inline only when the server cannot see your disk. Send every proof for the session in one request: they are \
     checked in a single Lean invocation, so one request costs one Mathlib import rather than one per proof. Retries \
     are the exception — resubmit only the ids that failed, since anything already accepted is never rechecked. A \
     proof that still contains `sorry` is a failure, not partial credit.";

const BATCHING_IS_NOT_YOUR_PROBLEM: &str = "Your proofs are concatenated into one file to be checked together, but you do not have to defend against that. \
     Imports are hoisted and de-duplicated, and each proof is wrapped in its own namespace, so identical theorem or \
     definition names across proofs cannot collide. Keep `import Mathlib` at the top of each proof and name things \
     whatever you like. Reported line numbers are rebased onto the file you submitted, not the batch.";

/// Substitute the placeholders, and unescape the doubled braces around them.
///
/// This is `str.format` over a fixed table, which is what Python used and why the
/// guidance is written with `{{` for a literal brace. A name nothing answers to
/// becomes `<name>` rather than failing: the guidance is served either way, and a
/// missing placeholder should read as an obvious gap, not a 500.
fn render(template: &str) -> String {
    let mut out = String::with_capacity(template.len());
    let mut rest = template;
    while let Some(open) = rest.find(['{', '}']) {
        out.push_str(&rest[..open]);
        let mut chars = rest[open..].chars();
        let brace = chars.next().unwrap_or('{');
        if chars.clone().next() == Some(brace) {
            out.push(brace);
            rest = &rest[open + brace.len_utf8() * 2..];
            continue;
        }
        if brace == '}' {
            out.push('}');
            rest = &rest[open + 1..];
            continue;
        }
        let Some(close) = rest[open..].find('}') else {
            out.push('{');
            rest = &rest[open + 1..];
            continue;
        };
        let name = &rest[open + 1..open + close];
        out.push_str(&placeholder(name));
        rest = &rest[open + close + 1..];
    }
    out.push_str(rest);
    out
}

fn placeholder(name: &str) -> String {
    PLACEHOLDERS
        .iter()
        .find(|(candidate, _)| *candidate == name)
        .map_or_else(|| format!("<{name}>"), |(_, value)| (*value).to_string())
}

fn kinds_block() -> String {
    let width = KINDS
        .iter()
        .map(|(kind, _)| kind.chars().count())
        .max()
        .unwrap_or(0);
    let lines: Vec<String> = KINDS
        .iter()
        .map(|(kind, meaning)| format!("  {kind:width$}  {meaning}"))
        .collect();
    format!(
        "Each property needs a `kind`, which is one of:\n{}",
        lines.join("\n")
    )
}

fn kind_names() -> String {
    KINDS
        .iter()
        .map(|(kind, _)| *kind)
        .collect::<Vec<_>>()
        .join(", ")
}

/// The heading and the body of a guidance file whose first line is its title.
fn titled(name: &str) -> (String, String) {
    let text = prompts::text(name);
    let (first, rest) = text.split_once('\n').unwrap_or((text, ""));
    (format!("## {first}"), rest.trim().to_string())
}

fn extract() -> String {
    let (kinds_placeholder, user) = (
        "%%KINDS%%",
        render(prompts::text("property_extraction_user")),
    );
    [
        "## Step 1 — separate pure logic from side effects".to_string(),
        prompts::text("decompose_system").trim().to_string(),
        render(prompts::text("decompose_user")),
        "## Step 2 — identify properties worth proving".to_string(),
        prompts::text("property_extraction_system")
            .trim()
            .to_string(),
        user.replace(kinds_placeholder, &kinds_block()),
        "## Step 3 — write the spec file".to_string(),
        SPEC_FILE_STEP.to_string(),
        CONTIGUOUS_SLICE.to_string(),
    ]
    .join("\n\n")
}

fn tactics() -> String {
    let (finite_heading, finite_body) = titled("finite_case_analysis");
    let (filter_heading, filter_body) = titled("filter_and_partition");
    [
        "## Rules that prevent the common failures".to_string(),
        prompts::text("proof_generation_system").trim().to_string(),
        render(prompts::text("proof_generation_user")),
        finite_heading,
        finite_body,
        filter_heading,
        filter_body,
        "## When Lean rejects a proof".to_string(),
        render(prompts::text("proof_retry_user")),
        AFTER_A_REJECTION.to_string(),
    ]
    .join("\n\n")
}

fn formalize() -> String {
    [
        "## Writing the Lean".to_string(),
        prompts::text("autoformalize_system").trim().to_string(),
        render(prompts::text("property_formalize_and_prove_user")),
        "## Submitting".to_string(),
        SUBMITTING.to_string(),
        BATCHING_IS_NOT_YOUR_PROBLEM.to_string(),
    ]
    .join("\n\n")
}

/// The schema of a spec file, as the index describes it.
fn spec_file() -> Value {
    json!({
        "filename": "formal.properties.json (conventional; any path works)",
        "schema": {
            "version": 1,
            "properties": [{
                "id": "required — how a human reads the diff, e.g. 'fmt_elapsed/monotonicity'. \
                       Not part of the cache key: renaming keeps the cached proof.",
                "function": "required — the function this is about",
                "kind": format!("required — one of: {}", kind_names()),
                "formal": "required — the mathematical statement, e.g. 'forall x, f x <= x'",
                "description": "optional — one line of prose for a human reviewer",
                "preconditions": "optional — list of what must hold on inputs",
                "assumptions": "optional — list of modelling choices made",
                "source_file": "optional but recommended — path, relative to the spec file, \
                                that function_code came from",
                "function_code": "optional but recommended — the function's source, so formal \
                                  can tell you when it has changed underneath the property",
            }],
        },
        "notes": [
            "id, function, kind and formal identify the property. The cache key is derived from the \
             function source, the kind and the formal statement, so those three must stay stable \
             across runs for a proof to be reused; prose may change freely.",
            "Prose is not in the key, so a cache hit reports the description and assumptions recorded \
             when the proof was accepted. Read them — if that modelling is not yours, the hit is not \
             the property you meant.",
        ],
    })
}

/// The workflow, the spec schema, and what else can be asked for.
#[must_use]
pub fn index() -> Value {
    json!({
        "workflow": WORKFLOW,
        "spec_file": spec_file(),
        "stale": STALE_ADVICE,
        "sessions": SESSION_LIFETIME,
        "openapi": OPENAPI,
        "verified": WHAT_VERIFIED_MEANS,
        "topics": TOPICS
            .iter()
            .map(|(name, summary)| ((*name).to_string(), json!(summary)))
            .collect::<serde_json::Map<String, Value>>(),
    })
}

/// The instructions for one phase, or nothing for a topic that does not exist.
#[must_use]
pub fn topic(name: &str) -> Option<String> {
    match name {
        "extract" => Some(extract()),
        "formalize" => Some(formalize()),
        "tactics" => Some(tactics()),
        _ => None,
    }
}

/// Every topic that can be asked for, in the order the index lists them.
#[must_use]
pub fn topic_names() -> Vec<&'static str> {
    TOPICS.iter().map(|(name, _)| *name).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_placeholder_becomes_what_it_stands_for() {
        assert_eq!(
            render("a {code} b"),
            "a <the full source of the file under test> b"
        );
    }

    #[test]
    fn a_doubled_brace_becomes_a_single_one() {
        assert_eq!(render("{{'a': 1}}"), "{'a': 1}");
        assert_eq!(
            render("{{{code}}}"),
            "{<the full source of the file under test>}"
        );
    }

    #[test]
    fn a_placeholder_nothing_answers_to_reads_as_a_gap() {
        assert_eq!(render("a {nowhere} b"), "a <nowhere> b");
    }

    #[test]
    fn text_with_no_braces_at_all_is_untouched() {
        assert_eq!(render("nothing to see"), "nothing to see");
    }

    #[test]
    fn the_kinds_block_lines_up_on_the_longest_name() {
        let block = kinds_block();
        assert!(
            block.contains("  bound           a value is constrained"),
            "{block}"
        );
        assert!(
            block.contains("  counterexample  two concrete inputs"),
            "{block}"
        );
    }

    #[test]
    fn every_topic_the_index_lists_can_be_fetched() {
        for name in topic_names() {
            assert!(topic(name).is_some_and(|text| !text.is_empty()), "{name}");
        }
    }

    #[test]
    fn a_topic_that_does_not_exist_is_nothing() {
        assert_eq!(topic("no-such-topic"), None);
    }

    #[test]
    fn no_placeholder_survives_into_what_is_served() {
        for name in topic_names() {
            let served = topic(name).expect("the topic exists");
            assert!(!served.contains("%%KINDS%%"), "{name}");
        }
    }

    #[test]
    fn the_index_names_the_same_topics_it_can_serve() {
        let index = index();
        let listed = index["topics"].as_object().expect("an object");
        assert_eq!(listed.len(), topic_names().len());
        for name in topic_names() {
            assert!(listed.contains_key(name), "{name}");
        }
    }
}
