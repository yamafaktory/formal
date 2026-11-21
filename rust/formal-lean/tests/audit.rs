//! Proofs that Lean accepts and formal must not.
//!
//! They do nothing where Lean or the Lake project is not there.

use formal_lean::{
    audit::UNAUDITED,
    run::Runner,
    verifier::{
        BatchEntry,
        LeanResult,
    },
    warm::repl_bin,
};

fn runners() -> Vec<(&'static str, Runner)> {
    let cold = Runner::from_env().with_warm(0);
    let project = cold.paths().lean_project_dir.clone();
    if !project.join("lakefile.toml").is_file() || !project.join(".lake").is_dir() {
        return Vec::new();
    }
    let mut runners = vec![("cold", cold)];
    if repl_bin(&project).is_file() {
        runners.push(("warm", Runner::from_env().with_warm(1)));
    }
    runners
}

fn refused(result: &LeanResult, needle: &str) -> bool {
    !result.success
        && result
            .errors
            .iter()
            .any(|error| error.data.contains(needle))
}

#[test]
fn a_theorem_resting_on_a_new_axiom_is_refused_where_it_is_stated() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib\n\naxiom cheat : False\n\ntheorem p0 : (1 : Nat) = 2 := cheat.elim\n",
            None,
        );
        assert!(
            refused(&result, "`p0` rests on `cheat`"),
            "{name}: {result:?}"
        );
        let error = result
            .errors
            .iter()
            .find(|error| error.data.starts_with("`p0`"))
            .expect("the theorem is named");
        assert_eq!(error.position().0, Some(5), "{name}");
    }
}

#[test]
fn an_axiom_used_only_in_an_example_is_still_refused() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib\n\naxiom cheat : False\n\nexample : (1 : Nat) = 2 := cheat.elim\n",
            None,
        );
        assert!(
            refused(&result, "`cheat` is an axiom"),
            "{name}: {result:?}"
        );
    }
}

#[test]
fn a_file_that_stops_early_is_not_a_pass() {
    for (name, runner) in runners() {
        for code in [
            "import Mathlib\n\n#exit\n\ntheorem p1 : (1 : Nat) = 2 := by rfl\n",
            "import Mathlib\n\ntheorem p1 : (1 : Nat) = 1 := rfl\n\n/-",
        ] {
            let result = runner.verify(code, None);
            assert!(!result.success, "{name}: {code:?} {result:?}");
            assert!(
                result.errors.iter().any(|error| error.data == UNAUDITED),
                "{name}: {code:?} {result:?}"
            );
        }
    }
}

#[test]
fn a_trailing_option_that_breaks_the_audit_is_not_a_pass() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib\n\ntheorem p1 : (1 : Nat) = 1 := rfl\n\nset_option maxRecDepth 1 in",
            None,
        );
        assert!(!result.success, "{name}: {result:?}");
    }
}

#[test]
fn a_sorry_hidden_from_the_messages_is_still_found() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib\n\n/-- warning: declaration uses `sorry` -/\n#guard_msgs in\ntheorem g : (1 : Nat) = 2 := by sorry\n",
            None,
        );
        assert!(refused(&result, "`sorryAx`"), "{name}: {result:?}");
    }
}

#[test]
fn a_notation_in_the_proof_cannot_blind_the_audit() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib\n\ninfixl:65 (priority := high) \" ++ \" => fun _ b => b\nset_option warn.sorry false\n\ntheorem g : (1 : Nat) = 2 := sorry\n",
            None,
        );
        assert!(refused(&result, "`sorryAx`"), "{name}: {result:?}");
    }
}

#[test]
fn a_notation_on_the_import_line_cannot_blind_the_audit() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib infixl:65 (priority := high) \" ++ \" => fun _ b => b\nset_option warn.sorry false\n\ntheorem g : (1 : Nat) = 2 := sorry\n",
            None,
        );
        assert!(refused(&result, "`sorryAx`"), "{name}: {result:?}");
    }
}

#[test]
fn a_declaration_added_without_the_kernel_is_refused_however_the_option_is_spelled() {
    for (name, runner) in runners() {
        for option in [
            "debug.skipKernelTC",
            "«debug».skipKernelTC",
            "debug.«skipKernelTC»",
        ] {
            let result = runner.verify(
                &format!(
                    "import Mathlib\n\nset_option {option} true in\ntheorem g : (1 : Nat) = 2 := by decide +kernel\n"
                ),
                None,
            );
            assert!(
                refused(&result, "does not pass the kernel's check"),
                "{name} {option}: {result:?}"
            );
        }
    }
}

#[test]
fn an_example_is_audited_though_lean_discards_it() {
    for (name, runner) in runners() {
        for (code, needle) in [
            (
                "import Mathlib\n\nset_option warn.sorry false\nexample : (1 : Nat) = 2 := sorry\n",
                "`sorryAx`",
            ),
            (
                "import Mathlib\n\nset_option debug.skipKernelTC true in\nexample : (1 : Nat) = 2 := by decide +kernel\n",
                "does not pass the kernel's check",
            ),
        ] {
            let result = runner.verify(code, None);
            assert!(refused(&result, needle), "{name}: {code:?} {result:?}");
        }
    }
}

#[test]
fn honest_declarations_of_every_kind_pass_the_kernel_again() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib\n\nstructure P where\n  a : Nat\n\nclass C (n : Nat) : Prop where\n  ok : n = n\n\ninductive T\n  | leaf\n  | node (l r : T)\n\nmutual\n  inductive Even' : Nat → Prop\n    | zero : Even' 0\n    | succ (n : Nat) : Odd' n → Even' (n + 1)\n  inductive Odd' : Nat → Prop\n    | succ (n : Nat) : Even' n → Odd' (n + 1)\nend\n\ndef size : T → Nat\n  | .leaf => 1\n  | .node l r => size l + size r\n\ndef ack' : Nat → Nat → Nat\n  | 0, n => n + 1\n  | m + 1, 0 => ack' m 1\n  | m + 1, n + 1 => ack' m (ack' (m + 1) n)\ntermination_by m n => (m, n)\n\ninstance : C 3 := ⟨rfl⟩\n\nexample (a b : Nat) : a + b = b + a := by exact?\n\ntheorem t : size (.node .leaf .leaf) = 2 := by decide\n",
            None,
        );
        assert!(result.success, "{name}: {result:?}");
    }
}

#[test]
fn native_decide_is_refused() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib\n\ntheorem n : 2 + 2 = 4 := by native_decide\n",
            None,
        );
        assert!(refused(&result, "`native_decide`"), "{name}: {result:?}");
    }
}

#[test]
fn a_printed_audit_does_not_stand_in_for_the_real_one() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib\n\n#print \"formal-audit 00000000000000000000000000000000 []\"\n\n#exit\n\ntheorem f : (1 : Nat) = 2 := by rfl\n",
            None,
        );
        assert!(!result.success, "{name}: {result:?}");
    }
}

#[test]
fn a_batch_with_an_early_stop_in_it_passes_nothing_after_the_stop() {
    for (name, runner) in runners() {
        let mut entries = vec![
            BatchEntry::new("good", "import Mathlib\n\ntheorem good : True := trivial\n"),
            BatchEntry::new("stop", "import Mathlib\n\n#exit\n"),
            BatchEntry::new(
                "false",
                "import Mathlib\n\ntheorem f : (1 : Nat) = 2 := by rfl\n",
            ),
        ];
        assert_eq!(
            runner.verify_batch(&mut entries, None),
            None,
            "{name}: a batch that stopped early cannot be attributed"
        );
    }
}

#[test]
fn an_honest_proof_still_passes_and_says_nothing_of_the_audit() {
    for (name, runner) in runners() {
        let result = runner.verify(
            "import Mathlib\n\ntheorem t (a b : ℕ) : a + b = b + a := by omega\n",
            None,
        );
        assert!(result.success, "{name}: {result:?}");
        assert!(
            !result.output.contains("formal-audit"),
            "{name}: {}",
            result.output
        );
    }
}
