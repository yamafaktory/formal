"""Tests for lean_verifier — hint logic, syntax check, auto-tactic substitution."""

import json
import time

from formal.lean_verifier import (
    BatchEntry,
    LeanResult,
    _rebase,
    _split_imports,
    as_auto_tactic_attempt,
    as_premise_search,
    build_batch,
    check_syntax,
    error_position,
    replace_proof,
    suggested_tactic,
    sweep_stale_temps,
    verify_batch,
    with_auto_tactics,
)

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

    def test_omega_on_a_string_literal_length(self):
        hint = make_result('omega could not prove the goal:\nwhere\n a := ↑"WEIGHTED_SUM((".length').hint_for_error()
        assert "string literal" in hint
        assert "from rfl" in hint

    def test_omega_on_a_list_length_is_not_told_about_string_literals(self):
        """The regression: any omega failure mentioning .length got the string-literal advice.

        This one is a list length with an unreduced pair projection. The string hint sends
        the reader after `show "PREFIX".length = N from rfl`, which cannot apply here — and
        on the LLM path that misdirection costs a retry.
        """
        hint = make_result(
            "omega could not prove the goal:\n"
            "a possible counterexample may satisfy the constraints\n"
            "  c - d - e ≥ 1\n"
            "where\n"
            " b := ↑(List.filter p t, List.filter (not ∘ p) t).2.length\n"
            " c := ↑t.length\n"
            " d := ↑(List.filter p t).length"
        ).hint_for_error()
        assert "string literal" not in hint
        assert "from rfl" not in hint
        assert "opaque" in hint

    def test_omega_without_any_length_still_gets_help(self):
        hint = make_result("omega could not prove the goal:\nwhere\n a := ↑(f x)").hint_for_error()
        assert "linear integer arithmetic" in hint

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

    def test_a_capitalised_unknown_identifier_is_not_generic(self):
        """Lean 4.29 says "Unknown identifier"; the guard listed only the lowercase form.

        The same guard already carried both casings of "Unknown constant", so the
        neighbour had been fixed once and this one missed.
        """
        hint = make_result("Unknown identifier `made_up_lemma`").hint_for_error()
        assert not hint.startswith("Review Lean 4 syntax")
        assert "guess" in hint

    def test_a_guessed_lemma_is_not_reported_as_a_missing_hypothesis(self):
        hint = make_result("Unknown identifier `made_up_lemma`").hint_for_error()
        assert "local context" not in hint

    def test_a_missing_hypothesis_still_reads_as_one(self):
        hint = make_result("unknown identifier `h2`").hint_for_error()
        assert "local context" in hint

    def test_split_ifs_advice_only_appears_when_split_ifs_does(self):
        assert "split_ifs" not in make_result("unknown identifier `h2`").hint_for_error()
        assert "split_ifs" in make_result("unknown identifier `h2`, split_ifs with h1").hint_for_error()

    def test_a_failing_tactic_is_named(self):
        """Lean 4.29 reports "Tactic `x` failed"; no branch matched that shape at all."""
        hint = make_result("Tactic `rfl` failed: The left-hand side\n  l.reverse\nis not").hint_for_error()
        assert "`rfl`" in hint
        assert "definitionally equal" in hint

    def test_a_failing_decide_is_told_why_it_is_the_wrong_tactic(self):
        hint = make_result("Tactic `decide` failed: maximum recursion depth").hint_for_error()
        assert "decide" in hint
        assert "recursion" in hint or "ground" in hint

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


class TestSweepStaleTemps:
    """Scratch files stranded by a killed run must not accumulate."""

    def _aged(self, path, seconds_old):
        import os as _os

        path.write_text("import Mathlib\n")
        stamp = time.time() - seconds_old
        _os.utime(path, (stamp, stamp))
        return path

    def test_removes_a_stranded_file(self, tmp_path):
        old = self._aged(tmp_path / "tmp_dead.lean", 7200)
        sweep_stale_temps(tmp_path)
        assert not old.exists()

    def test_keeps_a_file_from_a_live_run(self, tmp_path):
        fresh = self._aged(tmp_path / "tmp_live.lean", 5)
        sweep_stale_temps(tmp_path)
        assert fresh.exists()

    def test_leaves_real_lean_sources_alone(self, tmp_path):
        source = self._aged(tmp_path / "Warmup.lean", 7200)
        keep = self._aged(tmp_path / ".gitkeep", 7200)
        sweep_stale_temps(tmp_path)
        assert source.exists()
        assert keep.exists()

    def test_missing_directory_is_harmless(self, tmp_path):
        sweep_stale_temps(tmp_path / "absent")


class TestBuildBatch:
    """One Lean file from many proofs: imports hoisted, definitions isolated."""

    def _entry(self, key, code):
        return BatchEntry(key=key, lean_code=code)

    def test_hoists_and_dedupes_imports(self):
        entries = [
            self._entry("a", "import Mathlib\n\ntheorem a : True := trivial\n"),
            self._entry("b", "import Mathlib\nimport Mathlib.Tactic\n\ntheorem b : True := trivial\n"),
        ]
        source = build_batch(entries)
        assert source.splitlines()[:2] == ["import Mathlib", "import Mathlib.Tactic"]
        assert source.count("import Mathlib\n") == 1

    def test_imports_only_appear_at_the_top(self):
        entries = [self._entry("a", "import Mathlib\n\ntheorem a : True := trivial\n")]
        body = "\n".join(build_batch(entries).splitlines()[2:])
        assert "import " not in body

    def test_each_entry_is_namespaced(self):
        entries = [self._entry("a", "theorem a : True := trivial\n"), self._entry("b", "theorem b : True := trivial\n")]
        source = build_batch(entries)
        assert "namespace Batch0" in source and "end Batch0" in source
        assert "namespace Batch1" in source and "end Batch1" in source

    def test_line_ranges_point_at_each_body(self):
        entries = [
            self._entry("a", "import Mathlib\n\ntheorem a : True := trivial\n"),
            self._entry("b", "theorem b : False := sorry\n"),
        ]
        lines = build_batch(entries).splitlines()
        for entry, needle in zip(entries, ["theorem a", "theorem b"]):
            span = lines[entry.first_line - 1 : entry.last_line]
            assert any(needle in line for line in span)

    def test_supplies_an_import_when_none_given(self):
        assert build_batch([self._entry("a", "theorem a : True := trivial\n")]).startswith("import Mathlib")


class TestVerifyBatch:
    def _entries(self):
        return [
            BatchEntry(key="a", lean_code="import Mathlib\n\ntheorem a : True := trivial\n"),
            BatchEntry(key="b", lean_code="theorem b : False := sorry\n"),
        ]

    def test_no_entries_is_an_empty_result(self):
        assert verify_batch([]) == {}

    def test_errors_are_attributed_by_line(self, monkeypatch):
        entries = self._entries()
        build_batch(entries)  # populate line ranges the same way verify_batch does
        failing_line = entries[1].first_line

        def fake_verify(source, timeout=None):
            return LeanResult(
                success=False,
                output="boom",
                errors=[{"severity": "error", "data": "unsolved goals", "pos": {"line": failing_line}}],
            )

        monkeypatch.setattr("formal.lean_verifier.verify", fake_verify)
        results = verify_batch(entries)
        assert results["a"].success is True
        assert results["b"].success is False

    def test_all_succeed_when_lean_reports_nothing(self, monkeypatch):
        monkeypatch.setattr(
            "formal.lean_verifier.verify",
            lambda source, timeout=None: LeanResult(success=True, output="", errors=[]),
        )
        results = verify_batch(self._entries())
        assert all(r.success for r in results.values())

    def test_an_error_outside_every_namespace_falls_back(self, monkeypatch):
        """A bad hoisted import invalidates the batch, not one proof."""
        monkeypatch.setattr(
            "formal.lean_verifier.verify",
            lambda source, timeout=None: LeanResult(
                success=False,
                output="unknown package",
                errors=[{"severity": "error", "data": "unknown package", "pos": {"line": 1}}],
            ),
        )
        assert verify_batch(self._entries()) is None

    def test_a_failure_without_errors_falls_back(self, monkeypatch):
        """A timeout reports no per-line errors, so nothing can be attributed."""
        monkeypatch.setattr(
            "formal.lean_verifier.verify",
            lambda source, timeout=None: LeanResult(success=False, output="timed out", errors=[]),
        )
        assert verify_batch(self._entries()) is None


class TestStringPrefixHint:
    """The String-level prefix recipe was verified against Lean v4.29.0.

    Every String-level route fails there (startsWith goes through the slice
    pattern API), so the hint must steer to List Char rather than to a tactic.
    """

    def _hint(self, data):
        return LeanResult(success=False, output="", errors=[{"severity": "error", "data": data}]).hint_for_error()

    def test_fires_on_a_slice_pattern_error(self):
        data = "unsolved goals a b : String ⊢ String.Slice.Pattern.ForwardPattern.startsWith a (a ++ b).toSlice"
        assert "List Char" in self._hint(data)

    def test_fires_on_definitional_equality_for_startswith(self):
        data = "Tactic `rfl` failed: The left-hand side (a ++ b).startsWith a is not definitionally equal"
        assert "String.toList_append" in self._hint(data)

    def test_fires_on_unsolved_isprefixof_over_append(self):
        data = "unsolved goals ⊢ p.isPrefixOf (p ++ rest) = true"
        assert "List.isPrefixOf" in self._hint(data)

    def test_free_variable_error_about_strings_gets_the_prefix_hint(self):
        data = "Expected type must not contain free variables: String.isPrefixOf a b"
        assert "List Char" in self._hint(data)

    def test_free_variable_error_elsewhere_keeps_generic_advice(self):
        data = "Expected type must not contain free variables: n + m"
        hint = self._hint(data)
        assert "linarith" in hint
        assert "List Char" not in hint

    def test_recommends_tolist_over_data(self):
        hint = self._hint("(a ++ b).startsWith a is not definitionally equal")
        assert ".toList" in hint
        assert "NOT `.data`" in hint

    def test_warns_off_the_lemmas_that_do_not_exist(self):
        hint = self._hint("(a ++ b).startsWith a is not definitionally equal")
        for absent in ("String.isPrefixOf_iff", "String.isPrefixOf_append_left", "List.isPrefixOf_append_left"):
            assert absent in hint


class TestAsAutoTacticAttempt:
    """Swapping a model-written proof for the tactic chain, before paying for a retry."""

    def test_replaces_a_single_proof_body(self):
        code = "import Mathlib\n\ntheorem t (a b : Rat) (h : a <= b) : a <= b := by\n  exact h\n"
        result = as_auto_tactic_attempt(code)
        assert result.startswith("import Mathlib\n\ntheorem t (a b : Rat) (h : a <= b) : a <= b := by first |")
        assert "exact h" not in result

    def test_keeps_the_definitions_above_the_theorem(self):
        code = "import Mathlib\n\ndef clamp (x : Rat) : Rat := x\n\ntheorem t : True := by\n  trivial\n"
        result = as_auto_tactic_attempt(code)
        assert "def clamp (x : Rat) : Rat := x" in result

    def test_handles_a_sorry_placeholder(self):
        assert "sorry" not in as_auto_tactic_attempt("theorem t : True := by sorry\n")

    def test_refuses_when_two_proofs_are_present(self):
        code = "theorem a : True := by trivial\n\ntheorem b : True := by trivial\n"
        assert as_auto_tactic_attempt(code) is None

    def test_refuses_when_a_declaration_follows_the_proof(self):
        code = "theorem t : True := by\n  trivial\n\ndef after : Nat := 1\n"
        assert as_auto_tactic_attempt(code) is None

    def test_refuses_when_there_is_no_proof(self):
        assert as_auto_tactic_attempt("import Mathlib\n\ndef f : Nat := 1\n") is None

    def test_the_rewritten_proof_uses_the_closing_chain(self):
        result = as_auto_tactic_attempt("theorem t : True := by trivial\n")
        assert "(linarith; done)" in result and "(ring; done)" in result


class TestPremiseSearch:
    """`exact?` retrieves a lemma from Mathlib, where the tactic chain only guesses."""

    def test_replaces_the_proof_with_a_search(self):
        code = "import Mathlib\n\ntheorem t (a b : List Char) : a <+: (a ++ b) := by\n  exact rfl\n"
        assert as_premise_search(code).rstrip().endswith(":= by exact?")

    def test_refuses_the_same_cases_the_tactic_chain_refuses(self):
        assert as_premise_search("theorem a : True := by trivial\n\ntheorem b : True := by trivial\n") is None
        assert as_premise_search("theorem t : True := by trivial\n\ndef after : Nat := 1\n") is None

    def test_replace_proof_accepts_any_tactic(self):
        code = "theorem t : True := by\n  sorry\n"
        assert replace_proof(code, "exact trivial").rstrip().endswith(":= by exact trivial")


class TestSuggestedTactic:
    """Lean answers premise search with a `Try this:` message."""

    def _line(self, data):
        return json.dumps({"severity": "information", "data": data})

    def test_parses_the_bracketed_form_lean_emits(self):
        out = self._line("Try this:\n [apply] exact List.prefix_append a b")
        assert suggested_tactic(out) == "exact List.prefix_append a b"

    def test_parses_a_plain_suggestion(self):
        assert suggested_tactic(self._line("Try this: exact Nat.le_refl n")) == "exact Nat.le_refl n"

    def test_parses_a_non_json_line(self):
        assert suggested_tactic("Try this: exact foo") == "exact foo"

    def test_none_when_lean_suggested_nothing(self):
        assert suggested_tactic(self._line("unsolved goals ⊢ False")) is None

    def test_none_on_empty_output(self):
        assert suggested_tactic("") is None

    def test_the_first_suggestion_wins(self):
        out = self._line("Try this: exact first") + "\n" + self._line("Try this: exact second")
        assert suggested_tactic(out) == "exact first"

    def test_a_suggestion_ending_in_n_keeps_its_argument(self):
        """rstrip takes a character set: stripping "\\n" that way ate the trailing n."""
        assert suggested_tactic(self._line("Try this: exact Nat.le_refl n")) == "exact Nat.le_refl n"

    def test_only_the_first_line_of_a_suggestion_is_taken(self):
        out = self._line("Try this:\n [apply] exact foo bar\nsome trailing noise")
        assert suggested_tactic(out) == "exact foo bar"


# ── error positions ───────────────────────────────────────────────────────────


class TestErrorPosition:
    """Lean reports positions under `pos`; the checker read flat `line`/`col` keys,
    so every failure came back positionless — with a batch that is bisecting blind."""

    def test_reads_the_position_lean_actually_sends(self):
        assert error_position({"pos": {"line": 12, "column": 4}}) == (12, 4)

    def test_falls_back_to_flat_keys(self):
        assert error_position({"line": 7, "col": 1}) == (7, 1)

    def test_absent_position_is_none(self):
        assert error_position({"data": "boom"}) == (None, None)


class TestSplitImportsTracksSource:
    def test_body_lines_remember_where_they_came_from(self):
        imports, body, source_lines = _split_imports("import Mathlib\n\ntheorem t : True := by\n  trivial")
        assert imports == ["import Mathlib"]
        assert body == ["", "theorem t : True := by", "  trivial"]
        assert source_lines == [2, 3, 4]

    def test_an_import_lower_down_still_shifts_the_rest(self):
        code = "theorem a : True := by trivial\nimport Foo\ntheorem b : True := by trivial"
        _, body, source_lines = _split_imports(code)
        assert len(body) == len(source_lines) == 2
        assert source_lines == [1, 3]


class TestRebase:
    """A batch line number points into a file the caller never saw."""

    def _entry(self):
        entry = BatchEntry(key="k", lean_code="import Mathlib\n\ntheorem t : True := by\n  trivial")
        build_batch([entry])
        return entry

    def test_a_batch_position_becomes_a_position_in_the_submitted_proof(self):
        entry = self._entry()
        # the second body line, wherever build_batch happened to place it
        rebased = _rebase({"pos": {"line": entry.first_line + 1, "column": 3}}, entry)
        assert error_position(rebased) == (entry.source_lines[1], 3)

    def test_a_position_outside_the_entry_is_left_alone(self):
        entry = self._entry()
        original = {"pos": {"line": 9999, "column": 1}}
        assert _rebase(original, entry) == original

    def test_a_positionless_error_is_left_alone(self):
        entry = self._entry()
        assert _rebase({"data": "boom"}, entry) == {"data": "boom"}
