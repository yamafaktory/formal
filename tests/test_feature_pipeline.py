"""Tests for FeaturePipelineResult — a tool failure must never read as a disproof."""

import pytest

from formal.feature_pipeline import FeaturePipelineResult
from formal.results import PropertyResult


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

    def test_an_errored_property_prevents_full(self):
        """full must mean everything was checked — an errored property was not."""
        assert _result(["verified", "verified", "error"]).overall_score == "partial"

    def test_errors_are_excluded_from_the_denominator(self):
        # One proved, one disproved, one errored: 1/2 of what was checked, not 1/3.
        assert _result(["verified", "failed", "error"]).overall_score == "partial"

    def test_a_genuine_disproof_still_scores_failed(self):
        assert _result(["failed", "failed"]).overall_score == "failed"

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


class TestBatchedFirstAttempt:
    """Formalize in parallel, check every first attempt in one Lean run, retry per property."""

    def _property(self, index):
        from formal.feature_extractor import Property

        return Property(
            id=f"prop_{index}",
            description=f"property {index}",
            function="f",
            kind="bound",
            formal="",
        )

    def _feature(self, count):
        from formal.feature_extractor import DecomposedFeature, PureFunction

        return DecomposedFeature(
            feature_summary="a module",
            pure_functions=[PureFunction(name="f", code="def f(): pass", description="f")],
            impure_parts=[],
            properties=[],
        )

    def _formalization(self, prop):
        from formal.property_verifier import Formalization

        return Formalization(
            prop=prop,
            key=f"key-{prop.id}",
            proof_code=f"theorem {prop.id} : True := trivial",
            started_at=0.0,
        )

    def _run(self, monkeypatch, count, batch_return, prove_spy):
        import formal.feature_pipeline as fp

        props = [self._property(i) for i in range(count)]
        monkeypatch.setattr(fp, "decompose", lambda code, language="Python": self._feature(count))
        monkeypatch.setattr(fp, "extract_properties", lambda feature, language="Python": props)
        monkeypatch.setattr(fp, "formalize", lambda prop, fn, language="Python": self._formalization(prop))
        monkeypatch.setattr(fp, "verify_batch", batch_return)
        monkeypatch.setattr(fp, "prove", prove_spy)
        return fp.run_feature_pipeline("def f(): pass", parallel=False)

    def test_one_batch_covers_every_pending_property(self, monkeypatch):
        seen_batches = []

        def batch(entries, timeout=None):
            seen_batches.append([e.key for e in entries])
            return {e.key: LeanResultStub(True) for e in entries}

        received = []

        def prove(f, first_result=None, max_retries=None):
            received.append((f.key, first_result))
            return _prop("verified", f.prop.id)

        self._run(monkeypatch, 3, batch, prove)
        assert seen_batches == [["key-prop_0", "key-prop_1", "key-prop_2"]]
        assert all(first is not None for _, first in received)

    def test_a_single_property_skips_the_batch(self, monkeypatch):
        calls = []

        def batch(entries, timeout=None):
            calls.append(entries)
            return {}

        self._run(monkeypatch, 1, batch, lambda f, first_result=None, max_retries=None: _prop("verified", f.prop.id))
        assert calls == []

    def test_an_unattributable_batch_falls_back_to_individual_proofs(self, monkeypatch):
        received = []

        def prove(f, first_result=None, max_retries=None):
            received.append(first_result)
            return _prop("verified", f.prop.id)

        self._run(monkeypatch, 3, lambda entries, timeout=None: None, prove)
        assert received == [None, None, None]

    def test_the_batch_verdict_reaches_each_property(self, monkeypatch):
        def batch(entries, timeout=None):
            return {e.key: LeanResultStub(e.key != "key-prop_1") for e in entries}

        received = {}

        def prove(f, first_result=None, max_retries=None):
            received[f.key] = first_result.success
            return _prop("verified" if first_result.success else "failed", f.prop.id)

        result = self._run(monkeypatch, 3, batch, prove)
        assert received == {"key-prop_0": True, "key-prop_1": False, "key-prop_2": True}
        assert result.properties_verified == 2


class LeanResultStub:
    def __init__(self, success):
        self.success = success
        self.output = ""
        self.errors = []
