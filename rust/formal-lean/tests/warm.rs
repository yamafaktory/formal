//! A warm Lean against a cold one, on the same proofs.
//!
//! They do nothing where Lean, the Lake project or the REPL is not there.

use std::time::{
    Duration,
    Instant,
};

use formal_lean::{
    run::Runner,
    verifier::{
        LeanResult,
        suggested_tactic,
    },
    warm::{
        repl_bin,
        warm_command,
    },
};

fn runners() -> Option<(Runner, Runner)> {
    let cold = Runner::from_env().with_warm(0);
    let project = &cold.paths().lean_project_dir;
    let ready = project.join("lakefile.toml").is_file()
        && project.join(".lake").is_dir()
        && repl_bin(project).is_file();
    ready.then(|| (Runner::from_env().with_warm(1), cold))
}

type Verdict = (
    bool,
    Vec<(String, String, Option<u32>, Option<u32>)>,
    Option<String>,
);

fn verdict(result: &LeanResult) -> Verdict {
    (
        result.success,
        result
            .errors
            .iter()
            .map(|error| {
                let (line, column) = error.position();
                (
                    error.severity.clone(),
                    error.data.trim().to_string(),
                    line,
                    column,
                )
            })
            .collect(),
        suggested_tactic(&result.output),
    )
}

const CASES: &[&str] = &[
    "import Mathlib\n\ntheorem t : True := trivial\n",
    "import Mathlib\n\ntheorem t : (1 : Nat) = 2 := by rfl\n",
    "import Mathlib\n\ntheorem t : (1 : Nat) = 1 := by sorry\n",
    "import Mathlib\n\ntheorem bad (n : ℕ) : n + 1 = n := by omega\n",
    "import Mathlib\n\ntheorem ex (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := by exact?\n",
    "import Mathlib\n\ntheorem x : True := by exact (by trivial\n",
    "import Mathlib\n\ntheorem a : True := trivial\n\ntheorem b : False := by simp\n\ntheorem c : 2 ≤ 3 := by norm_num\n",
    "import Mathlib\r\n\r\ntheorem t : (1 : Nat) = 2 := by\r\n  rfl\r\n",
    "import Mathlib\n\ndef clamp (x : ℚ) : ℚ := max 0 (min 1 x)\n\ntheorem t (x : ℚ) : 0 ≤ clamp x := le_max_left _ _\n",
    "import Mathlib\n\ntheorem t : 1 = 1 := by exact not_a_lemma\n",
    "\nimport Mathlib\ntheorem t : 3 ∣ 12 := by decide\n",
];

#[test]
fn a_warm_lean_gives_the_verdict_a_cold_one_gives() {
    let Some((warm, cold)) = runners() else {
        return;
    };
    for code in CASES {
        assert!(warm_command(code).is_some(), "{code:?} is not checked warm");
        let warm_result = warm.verify(code, None);
        let cold_result = cold.verify(code, None);
        assert_eq!(
            verdict(&warm_result),
            verdict(&cold_result),
            "{code:?}\nwarm: {}\ncold: {}",
            warm_result.output,
            cold_result.output
        );
    }
}

#[test]
fn a_warm_check_does_not_pay_for_the_import() {
    let Some((warm, cold)) = runners() else {
        return;
    };
    let code = "import Mathlib\n\ntheorem t (a b : ℕ) : a + b = b + a := by omega\n";
    warm.warm_up();

    let started = Instant::now();
    assert!(cold.verify(code, None).success);
    let cold_took = started.elapsed();

    let started = Instant::now();
    assert!(warm.verify(code, None).success);
    let warm_took = started.elapsed();

    assert!(
        warm_took * 4 < cold_took,
        "warm {warm_took:?}, cold {cold_took:?}"
    );
}

#[test]
fn an_overrun_is_killed_and_the_next_proof_is_still_checked() {
    let Some((warm, _)) = runners() else {
        return;
    };
    let result = warm.verify(
        "import Mathlib\n\ntheorem t : True := by\n  sleep 60000\n  trivial\n",
        Some(Duration::from_secs(2)),
    );
    assert!(
        result.output.contains("timed out after 2s"),
        "{}",
        result.output
    );

    let result = warm.verify("import Mathlib\n\ntheorem t : True := trivial\n", None);
    assert!(result.success, "{}", result.output);
}

#[test]
fn one_check_leaves_nothing_behind_for_the_next() {
    let Some((warm, _)) = runners() else {
        return;
    };
    let defined = warm.verify(
        "import Mathlib\n\ntheorem leak_me : True := trivial\n",
        None,
    );
    assert!(defined.success, "{}", defined.output);
    let used = warm.verify("import Mathlib\n\nexample : True := leak_me\n", None);
    assert!(!used.success, "{}", used.output);
}
