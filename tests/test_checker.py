"""Tests for the LLM-free checker — the core an agent drives directly.

Two invariants matter here beyond correctness: a malformed proof must never cost a
Mathlib import, and an outcome must never carry the full Lean output. Both exist to
keep the caller's token bill down, and neither is visible from the return value.
"""

from unittest.mock import patch

from formal.checker import Outcome, Submission, can_cache, check_batch, fmt_elapsed
from formal.lean_verifier import LeanResult

_PROOF = "import Mathlib\ntheorem t : True := by trivial"


def _ok(output="ok"):
    return LeanResult(success=True, output=output)


def _fail(data="unknown identifier 'foo'", line=3, col=7, output="…thousands of tokens of Mathlib noise…"):
    return LeanResult(success=False, output=output, errors=[{"data": data, "line": line, "col": col}])


def _subs(*ids):
    return [Submission(id=i, lean_code=f"theorem {i} : True := by trivial") for i in ids]


class TestSyntaxScreening:
    def test_malformed_proof_never_reaches_lean(self):
        with (
            patch("formal.checker.check_syntax", return_value=(False, "unexpected token")),
            patch("formal.checker.verify") as verify,
            patch("formal.checker.verify_batch") as verify_batch,
        ):
            outcomes = check_batch(_subs("p1"))

        assert verify.call_count == 0
        assert verify_batch.call_count == 0
        assert outcomes[0].status == "failed"
        assert outcomes[0].error == "unexpected token"

    def test_only_the_malformed_one_is_screened_out(self):
        def syntax(code):
            return (False, "bad") if "p2" in code else (True, "")

        with (
            patch("formal.checker.check_syntax", side_effect=syntax),
            patch("formal.checker.verify", return_value=_ok()),
            patch("formal.checker.verify_batch", return_value=None),
        ):
            outcomes = {o.id: o for o in check_batch(_subs("p1", "p2", "p3"))}

        assert outcomes["p1"].status == "verified"
        assert outcomes["p2"].status == "failed"
        assert outcomes["p3"].status == "verified"


class TestBatching:
    def test_many_proofs_share_one_lean_run(self):
        attributed = {"p1": _ok(), "p2": _ok()}
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify") as verify,
            patch("formal.checker.verify_batch", return_value=attributed) as verify_batch,
        ):
            outcomes = check_batch(_subs("p1", "p2"))

        assert verify_batch.call_count == 1
        assert verify.call_count == 0
        assert all(o.status == "verified" for o in outcomes)

    def test_a_single_proof_skips_the_batch(self):
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify", return_value=_ok()) as verify,
            patch("formal.checker.verify_batch") as verify_batch,
        ):
            check_batch(_subs("p1"))

        assert verify_batch.call_count == 0
        assert verify.call_count == 1

    def test_unattributable_batch_falls_back_to_one_run_each(self):
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify", return_value=_ok()) as verify,
            patch("formal.checker.verify_batch", return_value=None),
        ):
            outcomes = check_batch(_subs("p1", "p2"))

        assert verify.call_count == 2
        assert all(o.status == "verified" for o in outcomes)


class TestOutcomes:
    def test_failure_carries_the_first_error_and_its_hint(self):
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify", return_value=_fail(data="no goals", line=4, col=2)),
            patch("formal.checker.verify_batch", return_value=None),
            patch("formal.checker.recover_without_llm", return_value=None),
        ):
            outcome = check_batch(_subs("p1"))[0]

        assert outcome.status == "failed"
        assert outcome.error == "no goals"
        assert outcome.line == 4
        assert outcome.col == 2
        assert outcome.hint

    def test_failure_omits_the_full_lean_output(self):
        """The token-efficiency contract: the caller gets one error, not the transcript."""
        noise = "x" * 5000
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify", return_value=_fail(output=noise)),
            patch("formal.checker.verify_batch", return_value=None),
            patch("formal.checker.recover_without_llm", return_value=None),
        ):
            outcome = check_batch(_subs("p1"))[0]

        assert noise not in str(outcome)

    def test_order_matches_the_submissions(self):
        def syntax(code):
            return (False, "bad") if "p2" in code else (True, "")

        with (
            patch("formal.checker.check_syntax", side_effect=syntax),
            patch("formal.checker.verify", return_value=_ok()),
            patch("formal.checker.verify_batch", return_value=None),
        ):
            outcomes = check_batch(_subs("p1", "p2", "p3"))

        assert [o.id for o in outcomes] == ["p1", "p2", "p3"]

    def test_verified_reports_no_error(self):
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify", return_value=_ok()),
            patch("formal.checker.verify_batch", return_value=None),
        ):
            outcome = check_batch(_subs("p1"))[0]

        assert outcome.verified
        assert outcome.error == ""
        assert outcome.hint == ""


class TestRecovery:
    def test_a_recovered_proof_replaces_the_submission(self):
        recovered = ("theorem p1 : True := by decide", _ok())
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify", return_value=_fail()),
            patch("formal.checker.verify_batch", return_value=None),
            patch("formal.checker.recover_without_llm", return_value=recovered),
        ):
            outcome = check_batch(_subs("p1"))[0]

        assert outcome.status == "verified"
        assert outcome.lean_code == "theorem p1 : True := by decide"

    def test_recovery_is_not_attempted_on_success(self):
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify", return_value=_ok()),
            patch("formal.checker.verify_batch", return_value=None),
            patch("formal.checker.recover_without_llm") as recover,
        ):
            check_batch(_subs("p1"))

        assert recover.call_count == 0

    def test_a_failed_recovery_leaves_the_original_verdict(self):
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify", return_value=_fail(data="still broken")),
            patch("formal.checker.verify_batch", return_value=None),
            patch("formal.checker.recover_without_llm", return_value=None),
        ):
            outcome = check_batch(_subs("p1"))[0]

        assert outcome.status == "failed"
        assert outcome.error == "still broken"


class TestFmtElapsed:
    def test_seconds(self):
        assert fmt_elapsed(3.14) == "3.1s"

    def test_minutes(self):
        assert fmt_elapsed(125) == "2m 5s"

    def test_exactly_a_minute(self):
        assert fmt_elapsed(60) == "1m 0s"


class TestOutcomeShape:
    def test_verified_property_tracks_status(self):
        assert Outcome(id="p", status="verified", lean_code="").verified
        assert not Outcome(id="p", status="failed", lean_code="").verified


class TestCanCache:
    def _outcome(self, **kw):
        base = dict(id="p1", status="verified", lean_code=_PROOF, checked=True)
        return Outcome(**{**base, **kw})

    def test_an_evidenced_proof_can_be_cached(self):
        assert can_cache(self._outcome())

    def test_a_failure_can_never_be_cached(self):
        assert not can_cache(self._outcome(status="failed"))

    def test_an_unchecked_verdict_can_never_be_cached(self):
        """`checked` is set only where a LeanResult becomes an outcome."""
        assert not can_cache(self._outcome(checked=False))

    def test_a_proof_containing_sorry_can_never_be_cached(self):
        assert not can_cache(self._outcome(lean_code="import Mathlib\ntheorem t : True := by sorry"))

    def test_text_that_is_not_lean_can_never_be_cached(self):
        assert not can_cache(self._outcome(lean_code="ok"))

    def test_a_real_check_marks_its_outcome_checked(self):
        with (
            patch("formal.checker.check_syntax", return_value=(True, "")),
            patch("formal.checker.verify", return_value=_ok()),
            patch("formal.checker.verify_batch", return_value=None),
        ):
            outcome = check_batch([Submission(id="p1", lean_code=_PROOF)])[0]

        assert outcome.checked

    def test_a_syntax_rejection_is_not_marked_checked(self):
        """Lean never ran, so nothing about that proof has been established."""
        with patch("formal.checker.check_syntax", return_value=(False, "bad")):
            outcome = check_batch([Submission(id="p1", lean_code="ok")])[0]

        assert not outcome.checked
