"""Tests for feature_extractor — JSON cleaning, property parsing, LLM fallbacks."""

import json
from unittest.mock import patch

import pytest

from formal.feature_extractor import (
    DecomposedFeature,
    PureFunction,
    _clean_json,
    decompose,
    extract_properties,
    looks_like_it_defines_functions,
)

# ── _clean_json ───────────────────────────────────────────────────────────────


class TestCleanJson:
    def test_plain_json_unchanged(self):
        raw = '{"key": "value"}'
        assert _clean_json(raw) == raw

    def test_strips_generic_code_fence(self):
        raw = '```\n{"key": "value"}\n```'
        assert _clean_json(raw) == '{"key": "value"}'

    def test_strips_json_code_fence(self):
        raw = '```json\n{"key": "value"}\n```'
        assert _clean_json(raw) == '{"key": "value"}'

    def test_strips_leading_whitespace(self):
        raw = '  \n  {"key": "value"}'
        assert _clean_json(raw.strip()) == '{"key": "value"}'

    def test_unclosed_fence_still_strips_opener(self):
        raw = '```json\n{"key": "value"}'
        result = _clean_json(raw)
        assert result.startswith("{")


# ── extract_properties ────────────────────────────────────────────────────────


_DEFAULT_FN = PureFunction(
    name="apply_discount",
    code="def apply_discount(p, d): return p * (1 - d)",
    description="applies discount",
)


def make_feature(pure_functions=None):
    return DecomposedFeature(
        feature_summary="computes a discount",
        pure_functions=[_DEFAULT_FN] if pure_functions is None else pure_functions,
        impure_parts=[],
        properties=[],
    )


def llm_response(properties: list[dict]) -> str:
    return json.dumps({"properties": properties})


VALID_PROPERTY = {
    "id": "prop_1",
    "description": "price is always positive",
    "function": "apply_discount",
    "kind": "bound",
    "formal": "forall p d, 0 < p -> 0 <= d <= 1 -> 0 < apply_discount(p, d)",
    "preconditions": ["price > 0", "0 <= discount <= 1"],
    "assumptions": ["floats as rationals"],
    "verifiable": True,
    "unverifiable_reason": "",
}


class TestExtractProperties:
    def test_returns_empty_when_no_pure_functions(self):
        feature = make_feature(pure_functions=[])
        result = extract_properties(feature)
        assert result == []

    def test_parses_valid_property(self):
        with patch("formal.feature_extractor.call_llm", return_value=llm_response([VALID_PROPERTY])):
            props = extract_properties(make_feature())
        assert len(props) == 1
        p = props[0]
        assert p.id == "prop_1"
        assert p.description == "price is always positive"
        assert p.kind == "bound"
        assert p.verifiable is True
        assert p.preconditions == ["price > 0", "0 <= discount <= 1"]
        assert p.assumptions == ["floats as rationals"]

    def test_parses_unverifiable_property(self):
        unverifiable = {**VALID_PROPERTY, "verifiable": False, "unverifiable_reason": "depends on reference equality"}
        with patch("formal.feature_extractor.call_llm", return_value=llm_response([unverifiable])):
            props = extract_properties(make_feature())
        assert props[0].verifiable is False
        assert props[0].unverifiable_reason == "depends on reference equality"

    def test_defaults_verifiable_to_true_when_missing(self):
        prop = {k: v for k, v in VALID_PROPERTY.items() if k not in ("verifiable", "unverifiable_reason")}
        with patch("formal.feature_extractor.call_llm", return_value=llm_response([prop])):
            props = extract_properties(make_feature())
        assert props[0].verifiable is True

    def test_returns_empty_on_json_parse_error(self):
        with patch("formal.feature_extractor.call_llm", return_value="not valid json"):
            props = extract_properties(make_feature())
        assert props == []

    def test_retries_once_on_json_parse_error(self):
        responses = iter(["not valid json", llm_response([VALID_PROPERTY])])
        with patch("formal.feature_extractor.call_llm", side_effect=responses):
            props = extract_properties(make_feature())
        assert len(props) == 1

    def test_gives_up_after_two_parse_errors(self):
        with patch("formal.feature_extractor.call_llm", return_value="not valid json"):
            props = extract_properties(make_feature())
        assert props == []

    def test_returns_empty_on_llm_returning_empty_properties(self):
        with patch("formal.feature_extractor.call_llm", return_value=llm_response([])):
            props = extract_properties(make_feature())
        assert props == []

    def test_strips_code_fence_from_llm_response(self):
        fenced = f"```json\n{llm_response([VALID_PROPERTY])}\n```"
        with patch("formal.feature_extractor.call_llm", return_value=fenced):
            props = extract_properties(make_feature())
        assert len(props) == 1

    def test_fallback_id_when_missing(self):
        prop = {k: v for k, v in VALID_PROPERTY.items() if k != "id"}
        with patch("formal.feature_extractor.call_llm", return_value=llm_response([prop])):
            props = extract_properties(make_feature())
        assert props[0].id == "prop_1"

    def test_fallback_ids_are_one_based_and_never_collide(self):
        """A 0-based fallback made the second property collide with the model's prop_1."""
        first = {**VALID_PROPERTY, "id": "prop_1"}
        second = {k: v for k, v in VALID_PROPERTY.items() if k != "id"}
        with patch("formal.feature_extractor.call_llm", return_value=llm_response([first, second])):
            props = extract_properties(make_feature())
        assert [p.id for p in props] == ["prop_1", "prop_2"]

    def test_duplicate_ids_from_the_model_are_made_unique(self):
        dup = {**VALID_PROPERTY, "id": "same"}
        with patch("formal.feature_extractor.call_llm", return_value=llm_response([dup, dict(dup)])):
            props = extract_properties(make_feature())
        assert len({p.id for p in props}) == 2

    def test_blank_ids_fall_back_rather_than_colliding(self):
        blank = {**VALID_PROPERTY, "id": "  "}
        with patch("formal.feature_extractor.call_llm", return_value=llm_response([blank, dict(blank)])):
            props = extract_properties(make_feature())
        assert [p.id for p in props] == ["prop_1", "prop_2"]

    def test_passes_language_to_prompt(self):
        with patch("formal.feature_extractor.call_llm", return_value=llm_response([])) as mock_llm:
            extract_properties(make_feature(), language="Kotlin")
        call_args = mock_llm.call_args[0][1]  # second positional arg = user prompt
        assert "Kotlin" in call_args


class TestLooksLikeItDefinesFunctions:
    """Guards the retry that catches a decomposition returning nothing."""

    @pytest.mark.parametrize(
        "code",
        [
            "def clamp(x, lo, hi):\n    return max(lo, min(x, hi))\n",
            "fn clamp(x: i32) -> i32 { x }\n",
            "func Clamp(x int) int { return x }\n",
            "function clamp(x) { return x; }\n",
            "public int clamp(int x) {\n  return x;\n}\n",
            "const clamp = (x) => Math.max(0, x);\n",
            "pub fn clamp(x: i32) i32 {\n    return x;\n}\n",
        ],
    )
    def test_detects_definitions_across_languages(self, code):
        assert looks_like_it_defines_functions(code) is True

    @pytest.mark.parametrize(
        "code",
        ['PROMPT = """a long string"""\n', "X = 1\nY = 2\n", "", "# just a comment\n"],
    )
    def test_ignores_files_without_definitions(self, code):
        assert looks_like_it_defines_functions(code) is False


class TestDecomposeRetry:
    def _response(self, names):
        functions = [{"name": n, "code": f"def {n}(): pass", "description": n} for n in names]
        return json.dumps({"feature_summary": "s", "pure_functions": functions, "impure_parts": []})

    def test_an_empty_result_on_a_file_with_functions_is_retried(self):
        responses = [self._response([]), self._response(["clamp"])]
        with patch("formal.feature_extractor.call_llm", side_effect=responses) as mock_llm:
            feature = decompose("def clamp(x):\n    return x\n")
        assert [f.name for f in feature.pure_functions] == ["clamp"]
        assert mock_llm.call_count == 2

    def test_a_file_without_functions_is_not_retried(self):
        with patch("formal.feature_extractor.call_llm", return_value=self._response([])) as mock_llm:
            feature = decompose("CONSTANT = 1\n")
        assert feature.pure_functions == []
        assert mock_llm.call_count == 1

    def test_a_successful_decomposition_is_not_retried(self):
        with patch("formal.feature_extractor.call_llm", return_value=self._response(["clamp"])) as mock_llm:
            decompose("def clamp(x):\n    return x\n")
        assert mock_llm.call_count == 1

    def test_the_retry_is_attempted_only_once(self):
        with patch("formal.feature_extractor.call_llm", return_value=self._response([])) as mock_llm:
            feature = decompose("def clamp(x):\n    return x\n")
        assert feature.pure_functions == []
        assert mock_llm.call_count == 2
