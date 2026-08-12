"""Tests for FeaturePipelineResult — a tool failure must never read as a disproof."""

import pytest

from formal.feature_pipeline import FeaturePipelineResult
from formal.property_verifier import PropertyResult


def _prop(status, property_id="p"):
    return PropertyResult(
        property_id=property_id,
        description="a property",
        kind="bound",
        function="f",
        verified=status == "verified",
        lean_code="",
        lean_output="",
        retries=0,
        reason="NameError: name 'time' is not defined" if status == "error" else "",
        status=status,
        preconditions=[],
        assumptions=[],
    )


def _result(statuses):
    results = [_prop(s, f"p{i}") for i, s in enumerate(statuses)]
    return FeaturePipelineResult(
        feature_file="mod.py",
        feature_summary="a module",
        pure_functions=["f"],
        impure_parts=[],
        properties_found=len(results),
        properties_verified=sum(1 for r in results if r.status == "verified"),
        properties_unverifiable=sum(1 for r in results if r.status == "unverifiable"),
        results=results,
    )


class TestErroredCount:
    def test_counts_only_errors(self):
        assert _result(["verified", "failed", "error", "unverifiable", "error"]).properties_errored == 2

    def test_zero_when_nothing_errored(self):
        assert _result(["verified", "failed"]).properties_errored == 0


class TestScore:
    def test_a_crashed_run_scores_error_not_failed(self):
        """The regression: 10 internal errors used to render as 0/10 verified, 'failed'."""
        assert _result(["error"] * 10).overall_score == "error"

    def test_errors_are_excluded_from_the_denominator(self):
        # Two verifiable properties, both proved; the third only errored.
        assert _result(["verified", "verified", "error"]).overall_score == "full"

    def test_a_genuine_disproof_still_scores_failed(self):
        assert _result(["failed", "failed"]).overall_score == "failed"

    def test_partial_is_unaffected_by_an_error(self):
        assert _result(["verified", "failed", "error"]).overall_score == "partial"

    @pytest.mark.parametrize("statuses", [["unverifiable"], ["unverifiable", "unverifiable"]])
    def test_only_unverifiable_is_still_no_pure_logic(self, statuses):
        assert _result(statuses).overall_score == "no_pure_logic"


class TestSummary:
    def test_errors_are_named_and_disclaimed(self):
        text = _result(["verified", "error"]).summary()
        assert "1 errored" in text
        assert "tool failure, not a verdict" in text

    def test_errored_properties_use_a_distinct_marker(self):
        text = _result(["error"]).summary()
        assert "  ! [bound]" in text

    def test_a_clean_run_says_nothing_about_errors(self):
        text = _result(["verified", "failed"]).summary()
        assert "errored" not in text
        assert "tool failure" not in text
