//! What Lean said, and what to hand it next.
//!
//! Everything here is about the text of a proof and the text of a diagnostic.
//! Running Lean itself comes next; this is what surrounds it — screening a proof
//! before paying for an invocation, assembling several proofs into one file so
//! Mathlib is imported once, and moving a position in that file back into the
//! proof the caller actually wrote.

use std::{
    fs,
    path::Path,
    sync::OnceLock,
    time::{
        Duration,
        SystemTime,
    },
};

use formal_core::{
    hints::Table,
    pystr,
};
use regex::Regex;
use serde::Deserialize;

/// Tried before asking anyone to write a proof.
///
/// Ordered fastest-first: `rfl` (instant), `omega` (linear Nat/Int), `norm_num`
/// (numeric), `linarith`/`ring` (rational and real arithmetic — the usual
/// modelling of floats), `decide` (finite decidable), `simp` (last resort).
///
/// Each alternative is followed by `done`: `first` commits to whichever branch
/// succeeds, and `norm_num` and `simp` succeed by making progress without closing
/// the goal, which would shadow every later alternative.
const AUTO_TACTIC_STEPS: [&str; 7] = [
    "rfl", "omega", "norm_num", "linarith", "ring", "decide", "simp",
];

/// A scratch file older than this was stranded by a killed run.
const STALE_TEMP_AGE: Duration = Duration::from_hours(1);

/// The keywords a Lean file must contain at least one of to be worth running.
const REQUIRED_KEYWORDS: [&str; 5] = ["import", "theorem", "lemma", "def", "example"];

/// The tactic chain, as it is written into a proof.
#[must_use]
pub fn auto_tactics() -> &'static str {
    static CHAIN: OnceLock<String> = OnceLock::new();
    CHAIN.get_or_init(|| {
        let alternatives: Vec<String> = AUTO_TACTIC_STEPS
            .iter()
            .map(|step| format!("({step}; done)"))
            .collect();
        format!("first | {}", alternatives.join(" | "))
    })
}

/// Where in a file Lean says something is wrong.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
pub struct Pos {
    /// One-based line.
    #[serde(default)]
    pub line: Option<u32>,
    /// Zero-based column.
    #[serde(default)]
    pub column: Option<u32>,
}

/// One diagnostic from `lean --json`.
///
/// Python carried the raw dictionary so that unknown keys survived a rebase.
/// Nothing downstream ever read one: what leaves the service is the message, the
/// line and the column, so those are what this holds.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
pub struct LeanError {
    /// `error`, `warning`, `information`.
    #[serde(default)]
    pub severity: String,
    /// What Lean said.
    #[serde(default)]
    pub data: String,
    /// Where it said it.
    #[serde(default)]
    pub pos: Option<Pos>,
    /// The older flat spelling of the line.
    #[serde(default)]
    pub line: Option<u32>,
    /// The older flat spelling of the column.
    #[serde(default)]
    pub col: Option<u32>,
}

impl LeanError {
    /// Lean reports a position under `pos`; older shapes used flat keys.
    ///
    /// The checker read the flat keys only, so every failure came back
    /// positionless — and with a batch, that is bisecting blind.
    #[must_use]
    pub fn position(&self) -> (Option<u32>, Option<u32>) {
        let pos = self.pos.clone().unwrap_or_default();
        (pos.line.or(self.line), pos.column.or(self.col))
    }

    fn rebased_to(&self, line: u32) -> Self {
        Self {
            pos: Some(Pos {
                line: Some(line),
                column: self.pos.as_ref().and_then(|pos| pos.column).or(self.col),
            }),
            line: None,
            ..self.clone()
        }
    }
}

/// The verdict on one Lean invocation.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LeanResult {
    /// Whether Lean accepted it.
    pub success: bool,
    /// Everything Lean printed.
    pub output: String,
    /// The diagnostics worth acting on.
    pub errors: Vec<LeanError>,
}

impl LeanResult {
    /// The diagnostic to answer, which is always the first.
    #[must_use]
    pub fn first_error(&self) -> Option<&LeanError> {
        self.errors.first()
    }

    /// The advice for the first diagnostic, or nothing when there is none.
    #[must_use]
    pub fn hint_for_error(&self, table: &Table) -> String {
        self.first_error()
            .map_or_else(String::new, |error| table.hint_for(&error.data))
    }
}

/// Fast pre-check before invoking the full Lean verifier.
#[must_use]
pub fn check_syntax(lean_code: &str) -> (bool, String) {
    if lean_code.trim().is_empty() {
        return (false, "Empty Lean code".to_string());
    }
    if !REQUIRED_KEYWORDS
        .iter()
        .any(|keyword| lean_code.contains(keyword))
    {
        return (
            false,
            "Code must contain at least one of: import, theorem, lemma, def, example".to_string(),
        );
    }
    (true, String::new())
}

fn declaration_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN.get_or_init(|| {
        Regex::new(r"(?m)^\s*(theorem|lemma|def|example|instance|abbrev)\b")
            .expect("the pattern is a literal")
    })
}

/// Swap a caller-written proof for `tactic`, or nothing if that would mean guessing.
///
/// Only a single proof is rewritten, and only when nothing follows it — anything
/// else would require knowing where one declaration ends and the next begins.
#[must_use]
pub fn replace_proof(lean_code: &str, tactic: &str) -> Option<String> {
    if lean_code.matches(":= by").count() != 1 {
        return None;
    }
    let (head, tail) = lean_code.split_once(":= by")?;
    if declaration_pattern().is_match(tail) {
        return None;
    }
    Some(format!("{head}:= by {tactic}\n"))
}

/// Worth trying before asking for another proof: the chain closes `rfl`,
/// arithmetic and `simp` goals.
#[must_use]
pub fn as_auto_tactic_attempt(lean_code: &str) -> Option<String> {
    replace_proof(lean_code, auto_tactics())
}

/// `exact?` searches Mathlib for a term closing the goal, and names what it finds.
///
/// Where the tactic chain guesses from a fixed list, this retrieves — which is the
/// failure that dominates in practice: not a wrong tactic, but not knowing which
/// lemma exists.
#[must_use]
pub fn as_premise_search(lean_code: &str) -> Option<String> {
    replace_proof(lean_code, "exact?")
}

/// Replace `sorry` placeholders with the tactic chain for a quick attempt.
#[must_use]
pub fn with_auto_tactics(lean_code: &str) -> String {
    lean_code
        .replace(":= by sorry", &format!(":= by {}", auto_tactics()))
        .replace("by\n  sorry", &format!("by {}", auto_tactics()))
}

fn suggestion_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN.get_or_init(|| {
        Regex::new(r"Try this:\s*(?:\[[^\]]*\]\s*)?(.+)").expect("the pattern is a literal")
    })
}

/// Pull the tactic out of Lean's `Try this:` suggestion.
#[must_use]
pub fn suggested_tactic(output: &str) -> Option<String> {
    for line in pystr::splitlines(output) {
        let data = serde_json::from_str::<serde_json::Value>(line)
            .ok()
            .and_then(|parsed| {
                parsed
                    .get("data")
                    .and_then(|d| d.as_str())
                    .map(ToString::to_string)
            })
            .unwrap_or_else(|| line.to_string());
        let Some(found) = suggestion_pattern().captures(&data) else {
            continue;
        };
        // `trim_matches` takes a set of characters, not a suffix — trimming "\n"
        // that way would eat a trailing n from `exact Nat.le_refl n`.
        let tactic = pystr::splitlines(&found[1])
            .first()
            .map(|first| first.trim().trim_matches('"').trim().to_string())
            .unwrap_or_default();
        if !tactic.is_empty() {
            return Some(tactic);
        }
    }
    None
}

/// Remove scratch files stranded by a killed run; live ones are far younger.
pub fn sweep_stale_temps(verify_dir: &Path) {
    let Ok(entries) = fs::read_dir(verify_dir) else {
        return;
    };
    let Some(cutoff) = SystemTime::now().checked_sub(STALE_TEMP_AGE) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if !name.starts_with("tmp_") || !name.ends_with(".lean") {
            continue;
        }
        if entry
            .metadata()
            .and_then(|meta| meta.modified())
            .is_ok_and(|at| at < cutoff)
        {
            let _ = fs::remove_file(&path);
        }
    }
}

/// One proof inside a batched Lean file, and where it ended up.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BatchEntry {
    /// What the caller knows this proof as.
    pub key: String,
    /// The proof as submitted.
    pub lean_code: String,
    /// The first line of its body in the assembled file.
    pub first_line: u32,
    /// The last line of its body in the assembled file.
    pub last_line: u32,
    /// Where each body line came from in the submitted proof.
    ///
    /// Imports are hoisted out of the batch, so the nth body line is rarely the
    /// nth line the caller wrote, and a position it cannot locate in its own file
    /// is worse than none.
    pub source_lines: Vec<u32>,
}

impl BatchEntry {
    /// A proof to be checked alongside others.
    #[must_use]
    pub fn new(key: impl Into<String>, lean_code: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            lean_code: lean_code.into(),
            ..Self::default()
        }
    }

    fn covers(&self, line: u32) -> bool {
        self.first_line <= line && line <= self.last_line
    }
}

/// Split off the imports, remembering where each surviving line started.
fn split_imports(lean_code: &str) -> (Vec<&str>, Vec<&str>, Vec<u32>) {
    let mut imports = Vec::new();
    let mut body = Vec::new();
    let mut source_lines = Vec::new();
    for (number, line) in pystr::splitlines(lean_code).into_iter().enumerate() {
        if line.trim_start().starts_with("import ") {
            imports.push(line);
        } else {
            body.push(line);
            source_lines.push(u32::try_from(number + 1).unwrap_or(u32::MAX));
        }
    }
    (imports, body, source_lines)
}

/// Assemble one Lean file from several independent proofs.
///
/// Imports are hoisted because Lean only accepts them at the top of a file, and
/// each proof is namespaced so identically named definitions cannot collide. Each
/// entry is told where its body landed.
pub fn build_batch(entries: &mut [BatchEntry]) -> String {
    let mut seen_imports: Vec<String> = Vec::new();
    let mut bodies: Vec<Vec<String>> = Vec::new();
    for entry in &mut *entries {
        let (imports, body, source_lines) = split_imports(&entry.lean_code);
        entry.source_lines = source_lines;
        for line in imports {
            let line = line.trim().to_string();
            if !seen_imports.contains(&line) {
                seen_imports.push(line);
            }
        }
        bodies.push(body.into_iter().map(ToString::to_string).collect());
    }

    let mut lines = seen_imports;
    if lines.is_empty() {
        lines.push("import Mathlib".to_string());
    }
    lines.push(String::new());

    for (index, entry) in entries.iter_mut().enumerate() {
        lines.push(format!("namespace Batch{index}"));
        entry.first_line = u32::try_from(lines.len() + 1).unwrap_or(u32::MAX);
        lines.extend(bodies[index].iter().cloned());
        entry.last_line = u32::try_from(lines.len()).unwrap_or(u32::MAX);
        lines.push(format!("end Batch{index}"));
        lines.push(String::new());
    }
    lines.join("\n")
}

/// Move a position from the concatenated batch back into the submitted proof.
fn rebase(error: &LeanError, entry: &BatchEntry) -> LeanError {
    let Some(line) = error.position().0 else {
        return error.clone();
    };
    let Some(index) = line.checked_sub(entry.first_line) else {
        return error.clone();
    };
    entry
        .source_lines
        .get(index as usize)
        .map_or_else(|| error.clone(), |source| error.rebased_to(*source))
}

/// Check several proofs in a single Lean invocation, paying one Mathlib import.
///
/// Returns per-key results, or nothing when the batch itself could not be run —
/// the caller then falls back to verifying each proof on its own.
///
/// `run` is what actually invokes Lean, which is what lets this be tested without
/// one; in the service it is the runner.
pub fn verify_batch<F>(entries: &mut [BatchEntry], run: F) -> Option<Vec<(String, LeanResult)>>
where
    F: FnOnce(&str) -> LeanResult,
{
    if entries.is_empty() {
        return Some(Vec::new());
    }

    let result = run(&build_batch(entries));

    // An error outside every namespace (a bad hoisted import, say) invalidates the
    // whole batch rather than any one proof.
    for error in &result.errors {
        let line = error.position().0.unwrap_or(0);
        if !entries.iter().any(|entry| entry.covers(line)) {
            return None;
        }
    }
    if !result.success && result.errors.is_empty() {
        return None;
    }

    Some(
        entries
            .iter()
            .map(|entry| {
                let errors: Vec<LeanError> = result
                    .errors
                    .iter()
                    .filter(|error| entry.covers(error.position().0.unwrap_or(0)))
                    .map(|error| rebase(error, entry))
                    .collect();
                let result = LeanResult {
                    success: errors.is_empty(),
                    output: if errors.is_empty() {
                        String::new()
                    } else {
                        result.output.clone()
                    },
                    errors,
                };
                (entry.key.clone(), result)
            })
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use std::{
        fs::File,
        time::UNIX_EPOCH,
    };

    use tempfile::TempDir;

    use super::*;

    fn table() -> &'static Table {
        Table::shipped().expect("the shipped table is valid")
    }

    fn failure(data: &str) -> LeanResult {
        LeanResult {
            success: false,
            output: data.to_string(),
            errors: vec![LeanError {
                severity: "error".to_string(),
                data: data.to_string(),
                line: Some(1),
                col: Some(0),
                pos: None,
            }],
        }
    }

    mod hint_for_error {
        use super::*;

        #[test]
        fn no_errors_is_no_advice() {
            assert_eq!(LeanResult::default().hint_for_error(table()), "");
        }

        #[test]
        fn a_failing_tactic_is_named() {
            let hint = failure("Tactic `rfl` failed: The left-hand side\n  l.reverse\nis not")
                .hint_for_error(table());
            assert!(hint.contains("`rfl`"), "{hint}");
            assert!(hint.contains("definitionally equal"), "{hint}");
        }

        #[test]
        fn only_the_first_error_is_answered() {
            let mut result = failure("no goals");
            result.errors.push(LeanError {
                data: "maximum recursion depth has been reached".to_string(),
                ..LeanError::default()
            });
            assert_eq!(result.hint_for_error(table()), table().hint_for("no goals"));
        }

        #[test]
        fn anything_unrecognised_still_gets_an_answer() {
            assert!(
                !failure("some completely unknown error xyz")
                    .hint_for_error(table())
                    .is_empty()
            );
        }
    }

    mod syntax_check {
        use super::*;

        #[test]
        fn nothing_at_all_is_refused() {
            assert!(!check_syntax("").0);
            assert!(!check_syntax("   \n  ").0);
        }

        #[test]
        fn a_declaration_of_any_kind_passes() {
            for code in [
                "import Mathlib\ntheorem foo : 1 = 1 := by rfl",
                "lemma bar : True := trivial",
                "def f (x : Nat) : Nat := x + 1",
            ] {
                assert!(check_syntax(code).0, "{code}");
            }
        }

        #[test]
        fn something_that_declares_nothing_is_refused_by_name() {
            let (ok, message) = check_syntax("x + 1 = 2");
            assert!(!ok);
            assert!(message.contains("theorem"), "{message}");
        }
    }

    mod rewriting {
        use super::*;

        #[test]
        fn a_single_proof_body_is_replaced() {
            let code =
                "import Mathlib\n\ntheorem t (a b : Rat) (h : a <= b) : a <= b := by\n  exact h\n";
            let result = as_auto_tactic_attempt(code).expect("one proof and nothing after it");
            assert!(result.starts_with(
                "import Mathlib\n\ntheorem t (a b : Rat) (h : a <= b) : a <= b := by first |"
            ));
            assert!(!result.contains("exact h"));
        }

        #[test]
        fn the_definitions_above_the_theorem_are_kept() {
            let code = "import Mathlib\n\ndef clamp (x : Rat) : Rat := x\n\ntheorem t : True := by\n  trivial\n";
            let result = as_auto_tactic_attempt(code).expect("one proof");
            assert!(result.contains("def clamp (x : Rat) : Rat := x"));
        }

        #[test]
        fn two_proofs_are_refused() {
            assert_eq!(
                as_auto_tactic_attempt(
                    "theorem a : True := by trivial\n\ntheorem b : True := by trivial\n"
                ),
                None
            );
        }

        #[test]
        fn a_declaration_after_the_proof_is_refused() {
            assert_eq!(
                as_auto_tactic_attempt(
                    "theorem t : True := by\n  trivial\n\ndef after : Nat := 1\n"
                ),
                None
            );
        }

        #[test]
        fn no_proof_at_all_is_refused() {
            assert_eq!(
                as_auto_tactic_attempt("import Mathlib\n\ndef f : Nat := 1\n"),
                None
            );
        }

        #[test]
        fn the_rewritten_proof_uses_the_closing_chain() {
            let result =
                as_auto_tactic_attempt("theorem t : True := by trivial\n").expect("one proof");
            assert!(result.contains("(linarith; done)"));
            assert!(result.contains("(ring; done)"));
        }

        #[test]
        fn premise_search_replaces_the_proof_with_a_search() {
            let code = "import Mathlib\n\ntheorem t (a b : List Char) : a <+: (a ++ b) := by\n  exact rfl\n";
            let result = as_premise_search(code).expect("one proof");
            assert!(result.trim_end().ends_with(":= by exact?"), "{result}");
        }

        #[test]
        fn replace_proof_accepts_any_tactic() {
            let result = replace_proof("theorem t : True := by\n  sorry\n", "exact trivial")
                .expect("one proof");
            assert!(
                result.trim_end().ends_with(":= by exact trivial"),
                "{result}"
            );
        }

        #[test]
        fn a_sorry_placeholder_is_swapped_inline_and_in_a_block() {
            assert!(!with_auto_tactics("theorem foo : 1 = 1 := by sorry").contains("sorry"));
            assert!(!with_auto_tactics("theorem foo : 1 = 1 := by\n  sorry").contains("sorry"));
        }

        #[test]
        fn a_proof_with_no_sorry_is_left_alone() {
            let code = "theorem foo : 1 = 1 := by rfl";
            assert_eq!(with_auto_tactics(code), code);
        }
    }

    mod suggestions {
        use super::*;

        fn line(data: &str) -> String {
            serde_json::json!({ "severity": "information", "data": data }).to_string()
        }

        #[test]
        fn the_bracketed_form_lean_emits_is_parsed() {
            let out = line("Try this:\n [apply] exact List.prefix_append a b");
            assert_eq!(
                suggested_tactic(&out).as_deref(),
                Some("exact List.prefix_append a b")
            );
        }

        #[test]
        fn a_plain_suggestion_is_parsed() {
            assert_eq!(
                suggested_tactic(&line("Try this: exact Nat.le_refl n")).as_deref(),
                Some("exact Nat.le_refl n")
            );
        }

        #[test]
        fn a_line_that_is_not_json_is_read_as_itself() {
            assert_eq!(
                suggested_tactic("Try this: exact foo").as_deref(),
                Some("exact foo")
            );
        }

        #[test]
        fn nothing_suggested_is_nothing_returned() {
            assert_eq!(suggested_tactic(&line("unsolved goals ⊢ False")), None);
            assert_eq!(suggested_tactic(""), None);
        }

        #[test]
        fn the_first_suggestion_wins() {
            let out = format!(
                "{}\n{}",
                line("Try this: exact first"),
                line("Try this: exact second")
            );
            assert_eq!(suggested_tactic(&out).as_deref(), Some("exact first"));
        }

        #[test]
        fn only_the_first_line_of_a_suggestion_is_taken() {
            let out = line("Try this:\n [apply] exact foo bar\nsome trailing noise");
            assert_eq!(suggested_tactic(&out).as_deref(), Some("exact foo bar"));
        }
    }

    mod stale_temps {
        use super::*;

        fn aged(dir: &Path, name: &str, seconds_old: u64) -> std::path::PathBuf {
            let path = dir.join(name);
            fs::write(&path, "import Mathlib\n").expect("the file is writable");
            let stamp = SystemTime::now() - Duration::from_secs(seconds_old);
            File::options()
                .write(true)
                .open(&path)
                .expect("the file opens")
                .set_modified(stamp)
                .expect("the timestamp is settable");
            path
        }

        #[test]
        fn a_stranded_file_is_removed_and_a_live_one_is_not() {
            let dir = TempDir::new().expect("a temporary directory");
            let dead = aged(dir.path(), "tmp_dead.lean", 7200);
            let live = aged(dir.path(), "tmp_live.lean", 5);
            sweep_stale_temps(dir.path());
            assert!(!dead.exists());
            assert!(live.exists());
        }

        #[test]
        fn real_lean_sources_are_left_alone() {
            let dir = TempDir::new().expect("a temporary directory");
            let source = aged(dir.path(), "Warmup.lean", 7200);
            let keep = aged(dir.path(), ".gitkeep", 7200);
            sweep_stale_temps(dir.path());
            assert!(source.exists());
            assert!(keep.exists());
        }

        #[test]
        fn a_missing_directory_is_harmless() {
            let dir = TempDir::new().expect("a temporary directory");
            sweep_stale_temps(&dir.path().join("absent"));
        }

        #[test]
        fn a_file_from_before_the_epoch_is_swept_rather_than_panicking() {
            let dir = TempDir::new().expect("a temporary directory");
            let path = dir.path().join("tmp_ancient.lean");
            fs::write(&path, "").expect("the file is writable");
            File::options()
                .write(true)
                .open(&path)
                .expect("the file opens")
                .set_modified(UNIX_EPOCH)
                .expect("the timestamp is settable");
            sweep_stale_temps(dir.path());
            assert!(!path.exists());
        }
    }

    mod batching {
        use super::*;

        fn entries() -> Vec<BatchEntry> {
            vec![
                BatchEntry::new("a", "import Mathlib\n\ntheorem a : True := trivial\n"),
                BatchEntry::new("b", "theorem b : False := sorry\n"),
            ]
        }

        #[test]
        fn imports_are_hoisted_and_deduplicated() {
            let mut entries = vec![
                BatchEntry::new("a", "import Mathlib\n\ntheorem a : True := trivial\n"),
                BatchEntry::new(
                    "b",
                    "import Mathlib\nimport Mathlib.Tactic\n\ntheorem b : True := trivial\n",
                ),
            ];
            let source = build_batch(&mut entries);
            let lines: Vec<&str> = source.lines().collect();
            assert_eq!(lines[..2], ["import Mathlib", "import Mathlib.Tactic"]);
            assert_eq!(source.matches("import Mathlib\n").count(), 1);
        }

        #[test]
        fn imports_only_appear_at_the_top() {
            let mut entries = vec![BatchEntry::new(
                "a",
                "import Mathlib\n\ntheorem a : True := trivial\n",
            )];
            let source = build_batch(&mut entries);
            let body: Vec<&str> = source.lines().skip(2).collect();
            assert!(!body.join("\n").contains("import "));
        }

        #[test]
        fn each_entry_is_namespaced() {
            let mut entries = entries();
            let source = build_batch(&mut entries);
            for index in 0..2 {
                assert!(source.contains(&format!("namespace Batch{index}")));
                assert!(source.contains(&format!("end Batch{index}")));
            }
        }

        #[test]
        fn the_line_range_points_at_each_body() {
            let mut entries = entries();
            let source = build_batch(&mut entries);
            let lines: Vec<&str> = source.lines().collect();
            for (entry, needle) in entries.iter().zip(["theorem a", "theorem b"]) {
                let span = &lines[entry.first_line as usize - 1..entry.last_line as usize];
                assert!(
                    span.iter().any(|line| line.contains(needle)),
                    "{needle} in {span:?}"
                );
            }
        }

        #[test]
        fn an_import_is_supplied_when_none_was_given() {
            let mut entries = vec![BatchEntry::new("a", "theorem a : True := trivial\n")];
            assert!(build_batch(&mut entries).starts_with("import Mathlib"));
        }

        #[test]
        fn body_lines_remember_where_they_came_from() {
            let (imports, body, source_lines) =
                split_imports("import Mathlib\n\ntheorem t : True := by\n  trivial");
            assert_eq!(imports, ["import Mathlib"]);
            assert_eq!(body, ["", "theorem t : True := by", "  trivial"]);
            assert_eq!(source_lines, [2, 3, 4]);
        }

        #[test]
        fn an_import_lower_down_still_shifts_the_rest() {
            let code = "theorem a : True := by trivial\nimport Foo\ntheorem b : True := by trivial";
            let (_, body, source_lines) = split_imports(code);
            assert_eq!(body.len(), 2);
            assert_eq!(source_lines, [1, 3]);
        }
    }

    mod rebasing {
        use super::*;

        fn entry() -> BatchEntry {
            let mut entries = vec![BatchEntry::new(
                "k",
                "import Mathlib\n\ntheorem t : True := by\n  trivial",
            )];
            build_batch(&mut entries);
            entries.remove(0)
        }

        fn at(line: u32, column: u32) -> LeanError {
            LeanError {
                pos: Some(Pos {
                    line: Some(line),
                    column: Some(column),
                }),
                ..LeanError::default()
            }
        }

        #[test]
        fn a_batch_position_becomes_a_position_in_the_submitted_proof() {
            let entry = entry();
            let rebased = rebase(&at(entry.first_line + 1, 3), &entry);
            assert_eq!(rebased.position(), (Some(entry.source_lines[1]), Some(3)));
        }

        #[test]
        fn a_position_outside_the_entry_is_left_alone() {
            let entry = entry();
            let original = at(9999, 1);
            assert_eq!(rebase(&original, &entry), original);
        }

        #[test]
        fn a_position_before_the_entry_is_left_alone() {
            let entry = entry();
            let original = at(1, 1);
            assert_eq!(rebase(&original, &entry), original);
        }

        #[test]
        fn a_positionless_error_is_left_alone() {
            let entry = entry();
            let original = LeanError {
                data: "boom".to_string(),
                ..LeanError::default()
            };
            assert_eq!(rebase(&original, &entry), original);
        }

        #[test]
        fn the_position_lean_actually_sends_wins_over_the_flat_one() {
            let error = LeanError {
                pos: Some(Pos {
                    line: Some(12),
                    column: Some(4),
                }),
                line: Some(7),
                col: Some(1),
                ..LeanError::default()
            };
            assert_eq!(error.position(), (Some(12), Some(4)));
        }

        #[test]
        fn the_flat_keys_are_still_read_when_there_is_no_pos() {
            let error = LeanError {
                line: Some(7),
                col: Some(1),
                ..LeanError::default()
            };
            assert_eq!(error.position(), (Some(7), Some(1)));
        }

        #[test]
        fn an_absent_position_is_nothing() {
            assert_eq!(LeanError::default().position(), (None, None));
        }
    }

    mod batched_verification {
        use super::*;

        fn entries() -> Vec<BatchEntry> {
            vec![
                BatchEntry::new("a", "import Mathlib\n\ntheorem a : True := trivial\n"),
                BatchEntry::new("b", "theorem b : False := sorry\n"),
            ]
        }

        fn keyed(results: Option<Vec<(String, LeanResult)>>) -> Vec<(String, bool)> {
            results
                .expect("the batch ran")
                .into_iter()
                .map(|(key, result)| (key, result.success))
                .collect()
        }

        #[test]
        fn no_entries_is_an_empty_result() {
            let ran = verify_batch(&mut [], |_| unreachable!("nothing to run"));
            assert_eq!(ran, Some(Vec::new()));
        }

        #[test]
        fn errors_are_attributed_by_line() {
            let mut entries = entries();
            build_batch(&mut entries);
            let failing_line = entries[1].first_line;
            let results = verify_batch(&mut entries, |_| LeanResult {
                success: false,
                output: "boom".to_string(),
                errors: vec![LeanError {
                    severity: "error".to_string(),
                    data: "unsolved goals".to_string(),
                    pos: Some(Pos {
                        line: Some(failing_line),
                        column: None,
                    }),
                    ..LeanError::default()
                }],
            });
            assert_eq!(
                keyed(results),
                [("a".to_string(), true), ("b".to_string(), false)]
            );
        }

        #[test]
        fn everything_succeeds_when_lean_reports_nothing() {
            let results = verify_batch(&mut entries(), |_| LeanResult {
                success: true,
                ..LeanResult::default()
            });
            assert_eq!(
                keyed(results),
                [("a".to_string(), true), ("b".to_string(), true)]
            );
        }

        #[test]
        fn an_error_outside_every_namespace_falls_back() {
            let results = verify_batch(&mut entries(), |_| LeanResult {
                success: false,
                output: "unknown package".to_string(),
                errors: vec![LeanError {
                    data: "unknown package".to_string(),
                    pos: Some(Pos {
                        line: Some(1),
                        column: None,
                    }),
                    ..LeanError::default()
                }],
            });
            assert_eq!(results, None);
        }

        #[test]
        fn a_failure_without_errors_falls_back() {
            let results = verify_batch(&mut entries(), |_| LeanResult {
                success: false,
                output: "timed out".to_string(),
                errors: Vec::new(),
            });
            assert_eq!(results, None);
        }

        #[test]
        fn a_passing_entry_carries_no_output_of_its_neighbours_failure() {
            let mut entries = entries();
            build_batch(&mut entries);
            let failing_line = entries[1].first_line;
            let results = verify_batch(&mut entries, |_| LeanResult {
                success: false,
                output: "boom".to_string(),
                errors: vec![LeanError {
                    data: "unsolved goals".to_string(),
                    pos: Some(Pos {
                        line: Some(failing_line),
                        column: None,
                    }),
                    ..LeanError::default()
                }],
            })
            .expect("the batch ran");
            assert_eq!(results[0].1.output, "");
            assert_eq!(results[1].1.output, "boom");
        }
    }
}
