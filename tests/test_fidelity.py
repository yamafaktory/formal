"""Tests for fidelity — the round-trip check on what a proved theorem actually says."""

import json
from unittest.mock import patch

import pytest

from formal import fidelity
from formal.results import PropertyResult


def _verdict(agrees, reason="because"):
    return json.dumps({"agrees": agrees, "reason": reason})


def _result(property_id="p1", status="verified", lean_code="theorem t : True := trivial"):
    return PropertyResult(
        property_id=property_id,
        description="the result stays within bounds",
        kind="bound",
        function="f",
        verified=status == "verified",
        lean_code=lean_code,
        lean_output="",
        retries=0,
        reason="",
        status=status,
        preconditions=[],
        assumptions=[],
    )


def _serial(work, items):
    return [work(item) for item in items]


class TestCheck:
    def test_agreement_is_recorded_as_ok(self):
        with patch("formal.fidelity.call_llm", side_effect=["it stays within bounds", _verdict(True)]):
            result = fidelity.check("the result stays within bounds", "theorem t : True := trivial")
        assert result.verdict == fidelity.OK
        assert result.back_translation == "it stays within bounds"

    def test_disagreement_is_recorded_with_a_reason(self):
        with patch("formal.fidelity.call_llm", side_effect=["it says 1 = 1", _verdict(False, "different claim")]):
            result = fidelity.check("the result stays within bounds", "theorem t : True := trivial")
        assert result.verdict == fidelity.DIVERGES
        assert result.reason == "different claim"

    def test_the_back_translation_never_sees_the_description(self):
        """Showing the model what the theorem should say would defeat the check."""
        seen = []

        def capture(system, user, model=None):
            seen.append(user)
            return "some description" if len(seen) == 1 else _verdict(True)

        with patch("formal.fidelity.call_llm", side_effect=capture):
            fidelity.check("a very distinctive phrase", "theorem t : True := trivial")
        assert "a very distinctive phrase" not in seen[0]

    def test_empty_lean_code_is_unchecked(self):
        with patch("formal.fidelity.call_llm") as llm:
            assert fidelity.check("d", "   ").verdict == fidelity.UNCHECKED
        llm.assert_not_called()

    def test_an_unparseable_verdict_does_not_claim_divergence(self):
        """A broken judge must not manufacture doubt about a proved property."""
        with patch("formal.fidelity.call_llm", side_effect=["a description", "not json at all"]):
            result = fidelity.check("d", "theorem t : True := trivial")
        assert result.verdict == fidelity.OK

    def test_a_second_check_is_served_from_cache(self):
        with patch("formal.fidelity.call_llm", side_effect=["a description", _verdict(True)]) as llm:
            first = fidelity.check("d", "theorem t : True := trivial")
            second = fidelity.check("d", "theorem t : True := trivial")
        assert llm.call_count == 2
        assert first.verdict == second.verdict == fidelity.OK

    def test_different_theorems_are_checked_separately(self):
        responses = ["one", _verdict(True), "two", _verdict(True)]
        with patch("formal.fidelity.call_llm", side_effect=responses) as llm:
            fidelity.check("d", "theorem a : True := trivial")
            fidelity.check("d", "theorem b : True := trivial")
        assert llm.call_count == 4


class TestAnnotate:
    def test_only_verified_properties_are_checked(self):
        results = [_result("p1", "verified"), _result("p2", "failed"), _result("p3", "unverifiable")]
        with patch("formal.fidelity.call_llm", side_effect=["a description", _verdict(True)]) as llm:
            fidelity.annotate(results, _serial)
        assert llm.call_count == 2
        assert results[0].fidelity == fidelity.OK
        assert results[1].fidelity == "unchecked"

    def test_divergences_are_counted_and_recorded(self):
        # Distinct theorems, or the second would legitimately reuse the first's entry.
        results = [
            _result("p1", lean_code="theorem a : True := trivial"),
            _result("p2", lean_code="theorem b : True := trivial"),
        ]
        responses = ["one", _verdict(False, "weaker claim"), "two", _verdict(True)]
        with patch("formal.fidelity.call_llm", side_effect=responses):
            diverged = fidelity.annotate(results, _serial)
        assert diverged == 1
        assert results[0].fidelity == fidelity.DIVERGES
        assert results[0].fidelity_reason == "weaker claim"

    def test_nothing_verified_makes_no_calls(self):
        with patch("formal.fidelity.call_llm") as llm:
            assert fidelity.annotate([_result("p1", "failed")], _serial) == 0
        llm.assert_not_called()

    def test_a_failing_check_leaves_the_property_unchecked(self):
        """The fidelity check is advisory — its own failure must not alter a verdict."""
        results = [_result("p1")]
        with patch("formal.fidelity.call_llm", side_effect=RuntimeError("backend down")):
            diverged = fidelity.annotate(results, _serial)
        assert diverged == 0
        assert results[0].fidelity == "unchecked"
        assert results[0].status == "verified"


class TestSummaryRendering:
    def _pipeline(self, results):
        from formal.feature_pipeline import FeaturePipelineResult

        return FeaturePipelineResult(
            feature_file="m.py",
            feature_summary="a module",
            pure_functions=["f"],
            impure_parts=[],
            properties_found=len(results),
            properties_verified=sum(1 for r in results if r.status == "verified"),
            properties_unverifiable=0,
            results=results,
        )

    def test_a_divergence_is_shown_with_the_back_translation(self):
        result = _result("p1")
        result.fidelity = fidelity.DIVERGES
        result.fidelity_reason = "the theorem assumes what it should prove"
        result.back_translation = "it asserts True"
        text = self._pipeline([result]).summary()
        assert "may not match this property" in text
        assert "the theorem assumes what it should prove" in text
        assert "it asserts True" in text

    def test_an_unchecked_run_says_nothing_about_fidelity(self):
        text = self._pipeline([_result("p1")]).summary()
        assert "fidelity" not in text.lower()
        assert "may not match" not in text

    @pytest.mark.parametrize("verdict", [fidelity.OK, "unchecked"])
    def test_agreeing_properties_are_not_flagged(self, verdict):
        result = _result("p1")
        result.fidelity = verdict
        assert "may not match" not in self._pipeline([result]).summary()

    def test_the_count_is_exposed(self):
        diverging = _result("p1", lean_code="theorem a : True := trivial")
        diverging.fidelity = fidelity.DIVERGES
        assert self._pipeline([diverging, _result("p2")]).properties_diverging == 1
