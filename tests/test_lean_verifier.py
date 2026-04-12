"""Tests for lean_verifier — hint logic, syntax check, auto-tactic substitution."""

from formal.lean_verifier import LeanResult, check_syntax, with_auto_tactics

# ── Helpers ───────────────────────────────────────────────────────────────────


def make_result(error_data: str) -> LeanResult:
    return LeanResult(
        success=False,
        output=error_data,
        errors=[{"severity": "error", "data": error_data, "line": 1, "col": 0}],
    )


# ── hint_for_error ────────────────────────────────────────────────────────────


class TestHintForError:
    def test_no_errors_returns_empty(self):
        result = LeanResult(success=True, output="", errors=[])
        assert result.hint_for_error() == ""

    def test_no_goals_after_simp(self):
        hint = make_result("no goals").hint_for_error()
        assert "simp" in hint
        assert "already closed" in hint

    def test_no_goals_in_cases_branch(self):
        hint = make_result("no goals\ncases branch").hint_for_error()
        assert "cases" in hint or "branch" in hint

    def test_split_ifs_no_if(self):
        hint = make_result("split_ifs requires an if-then-else but no if-then-else was found").hint_for_error()
        assert "split_ifs" in hint
        assert "obtain" in hint

    def test_constructor_not_applicable(self):
        hint = make_result("constructor\nno applicable constructor").hint_for_error()
        assert "conjunction" in hint or "constructor" in hint

    def test_simp_made_no_progress(self):
        hint = make_result("simp made no progress").hint_for_error()
        assert "simp" in hint
        assert "split_ifs" in hint or "unfold" in hint

    def test_unknown_identifier_local(self):
        hint = make_result("unknown identifier `h2`").hint_for_error()
        assert "h2" in hint
        assert "context" in hint or "introduced" in hint

    def test_unknown_constant_mathlib(self):
        hint = make_result("Unknown constant `List.some_made_up_lemma`").hint_for_error()
        assert "Mathlib" in hint or "simp" in hint

    def test_type_mismatch_true_eq_true(self):
        hint = make_result(
            "type mismatch\n  hb\nhas type\n  x.field = true\nbut is expected to have type\n  true = true"
        ).hint_for_error()
        assert "rfl" in hint
        assert "true = true" in hint

    def test_type_mismatch_bool(self):
        hint = make_result("type mismatch\nBool\n= true").hint_for_error()
        assert "decide" in hint or "Bool" in hint

    def test_type_mismatch_generic(self):
        hint = make_result("type mismatch\nsomething unrelated").hint_for_error()
        assert "types" in hint.lower() or "match" in hint.lower()

    def test_inhabited_instance(self):
        hint = make_result("failed to generate instance\n  Inhabited MyType").hint_for_error()
        assert "Inhabited" in hint
        assert "head!" in hint or "List.head?" in hint

    def test_sorry_in_proof(self):
        hint = make_result("declaration uses 'sorry'").hint_for_error()
        assert "sorry" in hint

    def test_function_expected_mem_cons_self(self):
        hint = make_result("function expected\nmem_cons_self applied to arguments").hint_for_error()
        assert "mem_cons_self" in hint
        assert "implicit" in hint or "simp" in hint

    def test_function_expected_dot_field(self):
        hint = make_result("function expected\n.id field access").hint_for_error()
        assert "space" in hint or "dot" in hint or ".field" in hint

    def test_application_type_mismatch_option(self):
        hint = make_result(
            "application type mismatch\nhas type\n  Option String\nbut is expected to have type\n  Option Nat"
        ).hint_for_error()
        assert "map" in hint or "Option" in hint

    def test_fallback_hint(self):
        hint = make_result("some completely unknown error xyz").hint_for_error()
        assert len(hint) > 0


# ── check_syntax ──────────────────────────────────────────────────────────────


class TestCheckSyntax:
    def test_empty_code_fails(self):
        ok, _ = check_syntax("")
        assert not ok

    def test_whitespace_only_fails(self):
        ok, _ = check_syntax("   \n  ")
        assert not ok

    def test_theorem_passes(self):
        ok, _ = check_syntax("import Mathlib\ntheorem foo : 1 = 1 := by rfl")
        assert ok

    def test_lemma_passes(self):
        ok, _ = check_syntax("lemma bar : True := trivial")
        assert ok

    def test_def_passes(self):
        ok, _ = check_syntax("def f (x : Nat) : Nat := x + 1")
        assert ok

    def test_no_keyword_fails(self):
        ok, msg = check_syntax("x + 1 = 2")
        assert not ok
        assert "import" in msg or "theorem" in msg


# ── with_auto_tactics ─────────────────────────────────────────────────────────


class TestWithAutoTactics:
    def test_replaces_sorry_inline(self):
        code = "theorem foo : 1 = 1 := by sorry"
        result = with_auto_tactics(code)
        assert "sorry" not in result
        assert "rfl" in result or "omega" in result

    def test_replaces_sorry_block(self):
        code = "theorem foo : 1 = 1 := by\n  sorry"
        result = with_auto_tactics(code)
        assert "sorry" not in result

    def test_no_sorry_unchanged(self):
        code = "theorem foo : 1 = 1 := by rfl"
        assert with_auto_tactics(code) == code
