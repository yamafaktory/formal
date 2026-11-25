use std::{
    fs,
    path::{
        Path,
        PathBuf,
    },
    process::ExitCode,
};

use formal_core::lean_spec::LeanSpec;
use formal_lean::{
    env::Env,
    logger,
};
use formal_server::AppState;
use formal_service::{
    checker::{
        Checker,
        Outcome,
        Status,
    },
    session::{
        Comparison,
        Origin,
        Session,
    },
};
use serde_json::Value;

use crate::{
    FAILED,
    REFUSED,
};

struct Proof {
    id: String,
    path: PathBuf,
    found: bool,
}

pub(crate) fn run(env: &Env, spec: &Path, proofs: &Path, answers: Option<&Path>) -> ExitCode {
    logger::silence();
    match check(env, spec, proofs, answers) {
        Ok((report, true)) => {
            println!("{report}");
            ExitCode::SUCCESS
        }
        Ok((report, false)) => {
            println!("{report}");
            ExitCode::from(FAILED)
        }
        Err(refusal) => {
            eprintln!("formal: {refusal}");
            ExitCode::from(REFUSED)
        }
    }
}

fn check(
    env: &Env,
    spec: &Path,
    proofs: &Path,
    answers: Option<&Path>,
) -> Result<(String, bool), String> {
    let path = fs::canonicalize(spec).map_err(|e| format!("{}: {e}", spec.display()))?;
    let spec = LeanSpec::load(&path.to_string_lossy()).map_err(|e| e.to_string())?;
    let answers = answers.map(read_answers).transpose()?;
    let state = AppState::resolve(env).map_err(|e| e.to_string())?;
    let session = state
        .sessions
        .open_spec(&state.runner, &state.cache, spec)
        .map_err(|e| e.to_string())?;
    let mut session = session
        .lock()
        .map_err(|_| "the session lock is poisoned".to_string())?;

    let files = proof_files(&session, proofs);
    let submitted: Vec<(String, String)> = files
        .iter()
        .filter(|proof| proof.found)
        .map(|proof| {
            fs::read_to_string(&proof.path)
                .map(|lean| (proof.id.clone(), lean))
                .map_err(|e| format!("{}: {e}", proof.path.display()))
        })
        .collect::<Result<_, _>>()?;
    let outcomes = session
        .check(
            &Checker::new(&state.runner, state.table),
            &state.cache,
            &submitted,
        )
        .map_err(|e| e.to_string())?;
    let comparison = answers
        .map(|answers| session.compare(&answers))
        .transpose()
        .map_err(|e| e.to_string())?;

    Ok((
        render(&session, &outcomes, comparison.as_ref(), &files),
        passed(&session, comparison.as_ref()),
    ))
}

fn read_answers(path: &Path) -> Result<Vec<(String, Vec<Value>)>, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let parsed: serde_json::Map<String, Value> = serde_json::from_str(&text).map_err(|e| {
        format!(
            "{}: {e}: expected {{\"<function>\": [answers]}}",
            path.display()
        )
    })?;
    parsed
        .into_iter()
        .map(|(function, answers)| match answers {
            Value::Array(answers) => Ok((function, answers)),
            _ => Err(format!(
                "{}: the answers for {function} are not a list",
                path.display()
            )),
        })
        .collect()
}

fn proof_files(session: &Session, proofs: &Path) -> Vec<Proof> {
    let Some(spec) = &session.lean_spec else {
        return Vec::new();
    };
    session
        .work_ids()
        .into_iter()
        .filter(|id| session.refuted.iter().all(|refuted| refuted.id != *id))
        .map(|id| {
            let name = id
                .strip_prefix(&format!("{}.", spec.namespace))
                .unwrap_or(id);
            let path = proofs.join(&spec.namespace).join(format!("{name}.lean"));
            Proof {
                id: id.to_string(),
                found: path.is_file(),
                path,
            }
        })
        .collect()
}

fn passed(session: &Session, comparison: Option<&Comparison>) -> bool {
    let compared = session.evaluated.iter().all(|function| {
        comparison.is_some_and(|comparison| comparison.matched.contains(&function.function))
    });
    session.complete() && session.refuted.is_empty() && compared
}

fn render(
    session: &Session,
    outcomes: &[Outcome],
    comparison: Option<&Comparison>,
    files: &[Proof],
) -> String {
    let mut lines = Vec::new();
    let mut hints: Vec<&str> = Vec::new();
    for spec in &session.specs {
        let id = spec.id.as_str();
        property(session, outcomes, files, id, &mut hints, &mut lines);
        if let Some(bound) = session.bounded.iter().find(|bound| bound.id == id) {
            lines.push(format!(
                "  held in every state up to depth {} ({} states)",
                bound.depth, bound.states
            ));
        }
        if let Some(step) = session.not_inductive.iter().find(|step| step.id == id) {
            lines.push(format!(
                "  not inductive: from {}, {} leads to {}",
                step.state, step.action, step.next
            ));
        }
    }
    if !session.inductive_together.is_empty() {
        lines.push(format!(
            "· inductive together, prove them in one induction: {}",
            session.inductive_together.join(", ")
        ));
    }
    compared(session, comparison, &mut lines);
    lines.push(summary(session, comparison));
    lines.join("\n")
}

fn property<'a>(
    session: &Session,
    outcomes: &'a [Outcome],
    files: &[Proof],
    id: &str,
    hints: &mut Vec<&'a str>,
    lines: &mut Vec<String>,
) {
    if let Some(refuted) = session.refuted.iter().find(|refuted| refuted.id == id) {
        lines.push(format!(
            "✗ {id}  refuted: {}",
            refuted.counterexample.join(", ")
        ));
        if !refuted.issue.is_empty() {
            lines.push(format!("  {}", refuted.issue));
        }
        return;
    }
    if session.verified.contains_key(id) {
        let how = match session.origin(id) {
            Origin::Cache => "cached",
            Origin::Recovered => "verified by formal's own tactics",
            Origin::Submitted => "verified",
        };
        lines.push(format!("✓ {id}  {how}"));
        return;
    }
    let Some(file) = files.iter().find(|file| file.id == id) else {
        return;
    };
    let Some(failed) = outcomes
        .iter()
        .find(|outcome| outcome.id == id && outcome.status == Status::Failed)
    else {
        lines.push(format!(
            "· {id}  no proof: write {} declaring `theorem {id}.holds : {id}`",
            file.path.display()
        ));
        return;
    };
    let place = match (failed.line, failed.col) {
        (Some(line), Some(col)) => format!("{}:{line}:{col}", file.path.display()),
        _ => file.path.display().to_string(),
    };
    lines.push(format!("✗ {id}  {place}"));
    lines.extend(failed.error.lines().map(|line| format!("    {line}")));
    if failed.hint.is_empty() {
        return;
    }
    if hints.contains(&failed.hint.as_str()) {
        lines.push("  hint: as above".to_string());
    } else {
        hints.push(&failed.hint);
        let mut hint = failed.hint.lines();
        lines.push(format!("  hint: {}", hint.next().unwrap_or_default()));
        lines.extend(hint.map(|line| format!("    {line}")));
    }
}

fn compared(session: &Session, comparison: Option<&Comparison>, lines: &mut Vec<String>) {
    for function in &session.evaluated {
        let name = &function.function;
        let differed =
            comparison.and_then(|found| found.differed.iter().find(|d| d.function == *name));
        let matched = comparison.is_some_and(|found| found.matched.contains(name));
        if let Some(difference) = differed {
            lines.push(format!(
                "✗ {name}  differs from {} at {}: spec {}, code {}",
                function.code, difference.input, difference.spec, difference.code
            ));
        } else if matched {
            lines.push(format!("✓ {name}  matches {}", function.code));
        } else {
            lines.push(format!(
                "· {name}  compare: run {} on {}, then pass --answers <file> holding {{\"{name}\": [answers]}}",
                function.code,
                Value::Array(function.inputs.clone())
            ));
        }
    }
}

fn summary(session: &Session, comparison: Option<&Comparison>) -> String {
    let holding = session.cached_ids().len();
    let total = session.specs.len();
    let mut parts = vec![format!("{holding} of {total} properties hold")];
    if !session.refuted.is_empty() {
        parts.push(format!("{} refuted", session.refuted.len()));
    }
    let functions = session.evaluated.len();
    if functions > 0 {
        let matched = comparison.map_or(0, |found| found.matched.len());
        parts.push(format!("{matched} of {functions} functions match the code"));
    }
    parts.join(", ")
}

#[cfg(test)]
mod tests {
    use std::{
        collections::HashMap,
        time::Instant,
    };

    use formal_core::{
        lean_spec::{
            Bound,
            Difference,
            Evaluated,
            Refutation,
        },
        property::PropertySpec,
    };
    use serde_json::json;

    use super::*;

    fn session(ids: &[&str]) -> Session {
        Session {
            id: "s".to_string(),
            created_at: Instant::now(),
            specs: ids
                .iter()
                .map(|id| PropertySpec {
                    id: (*id).to_string(),
                    ..PropertySpec::default()
                })
                .collect(),
            keys: HashMap::new(),
            verified: HashMap::new(),
            attempts: HashMap::new(),
            hits: HashMap::new(),
            stale: Vec::new(),
            recovered: Vec::new(),
            lean_spec: None,
            evaluated: Vec::new(),
            refuted: Vec::new(),
            bounded: Vec::new(),
            not_inductive: Vec::new(),
            inductive_together: Vec::new(),
        }
    }

    fn file(id: &str, found: bool) -> Proof {
        Proof {
            id: id.to_string(),
            path: PathBuf::from(format!("proofs/R/{}.lean", id.trim_start_matches("R."))),
            found,
        }
    }

    fn failure(id: &str, hint: &str) -> Outcome {
        Outcome {
            line: Some(4),
            col: Some(2),
            ..Outcome::rejected(id, "", "omega could not prove the goal\nb ≤ -1", hint)
        }
    }

    fn wrap() -> Evaluated {
        Evaluated {
            function: "R.wrap".to_string(),
            code: "ring.py wrap".to_string(),
            inputs: vec![json!([7, -3])],
            answers: vec![json!(1)],
        }
    }

    #[test]
    fn a_verified_property_is_one_line_and_the_run_passes() {
        let mut session = session(&["R.p"]);
        session.verified.insert("R.p".to_string(), String::new());
        assert_eq!(
            render(&session, &[], None, &[]),
            "✓ R.p  verified\n1 of 1 properties hold"
        );
        assert!(passed(&session, None));
    }

    #[test]
    fn a_failure_names_its_place_and_its_hint() {
        let session = session(&["R.p"]);
        let report = render(
            &session,
            &[failure("R.p", "reduce the term first")],
            None,
            &[file("R.p", true)],
        );
        assert_eq!(
            report,
            "✗ R.p  proofs/R/p.lean:4:2\n    omega could not prove the goal\n    b ≤ -1\n  hint: reduce the term first\n0 of 1 properties hold"
        );
        assert!(!passed(&session, None));
    }

    #[test]
    fn a_hint_already_given_is_not_repeated() {
        let session = session(&["R.p", "R.q"]);
        let report = render(
            &session,
            &[failure("R.p", "reduce it"), failure("R.q", "reduce it")],
            None,
            &[file("R.p", true), file("R.q", true)],
        );
        assert_eq!(report.matches("reduce it").count(), 1, "{report}");
        assert!(report.contains("  hint: as above"), "{report}");
    }

    #[test]
    fn a_missing_proof_names_the_file_and_the_theorem() {
        let session = session(&["R.p"]);
        let report = render(&session, &[], None, &[file("R.p", false)]);
        assert!(
            report.starts_with(
                "· R.p  no proof: write proofs/R/p.lean declaring `theorem R.p.holds : R.p`"
            ),
            "{report}"
        );
    }

    #[test]
    fn a_refuted_property_shows_its_counterexample_and_fails_the_run() {
        let mut session = session(&["R.p"]);
        session.refuted.push(Refutation {
            id: "R.p".to_string(),
            counterexample: vec!["x := 0".to_string()],
            issue: "0 < 0 does not hold".to_string(),
        });
        let report = render(&session, &[], None, &[]);
        assert!(
            report.starts_with("✗ R.p  refuted: x := 0\n  0 < 0 does not hold"),
            "{report}"
        );
        assert!(!passed(&session, None));
    }

    #[test]
    fn a_bound_is_shown_under_its_property() {
        let mut session = session(&["R.inv.always"]);
        session.bounded.push(Bound {
            id: "R.inv.always".to_string(),
            depth: 10,
            states: 42,
        });
        let report = render(&session, &[], None, &[file("R.inv.always", false)]);
        assert!(
            report.contains("\n  held in every state up to depth 10 (42 states)"),
            "{report}"
        );
    }

    #[test]
    fn a_function_without_answers_asks_for_them_and_fails_the_run() {
        let mut session = session(&[]);
        session.evaluated.push(wrap());
        let report = render(&session, &[], None, &[]);
        assert!(
            report.starts_with("· R.wrap  compare: run ring.py wrap on [[7,-3]], then pass --answers <file> holding {\"R.wrap\": [answers]}"),
            "{report}"
        );
        assert!(!passed(&session, None));
    }

    #[test]
    fn a_difference_names_the_input_and_both_answers() {
        let mut session = session(&[]);
        session.evaluated.push(wrap());
        let comparison = Comparison {
            matched: Vec::new(),
            differed: vec![Difference {
                function: "R.wrap".to_string(),
                input: json!([7, -3]),
                spec: json!(1),
                code: json!(-2),
            }],
        };
        let report = render(&session, &[], Some(&comparison), &[]);
        assert!(
            report.starts_with("✗ R.wrap  differs from ring.py wrap at [7,-3]: spec 1, code -2"),
            "{report}"
        );
        assert!(!passed(&session, Some(&comparison)));
    }

    #[test]
    fn a_matching_function_passes() {
        let mut session = session(&[]);
        session.evaluated.push(wrap());
        let comparison = Comparison {
            matched: vec!["R.wrap".to_string()],
            differed: Vec::new(),
        };
        assert_eq!(
            render(&session, &[], Some(&comparison), &[]),
            "✓ R.wrap  matches ring.py wrap\n0 of 0 properties hold, 1 of 1 functions match the code"
        );
        assert!(passed(&session, Some(&comparison)));
    }
}
