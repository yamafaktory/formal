"""Tests for the guide an agent reads before driving formal.

The point of rendering it from prompts.py is that the agent path and the LLM path
cannot give different advice. The tests that matter here are the ones that fail
when that stops being true, or when a template placeholder reaches an agent
unsubstituted and it tries to prove something about `{function_code}`.
"""

import json
import pathlib
import re

import pytest
from fastapi.testclient import TestClient

from formal import api, guide, prompts

PLACEHOLDER = re.compile(r"(?<!\{)\{(" + "|".join(guide.PLACEHOLDERS) + r")\}(?!\})")


@pytest.fixture
def client():
    return TestClient(api.app)


class TestIndex:
    def test_it_carries_the_workflow_and_the_schema(self):
        index = guide.index()
        assert index["workflow"]
        assert index["spec_file"]["schema"]["version"] == 1
        assert set(index["topics"]) == {"extract", "formalize", "tactics"}

    def test_the_workflow_names_the_endpoints_it_depends_on(self):
        steps = " ".join(guide.index()["workflow"])
        for endpoint in ("/guide/extract", "/guide/formalize", "/guide/tactics", "/session", "/check"):
            assert endpoint in steps

    def test_it_answers_the_questions_the_first_caller_had_to_work_out(self):
        """Each of these cost a live test agent turns it should not have spent."""
        blob = json.dumps(guide.index())
        assert "expires" in blob, "sessions are ephemeral and a 404 does not say so"
        assert "must be absolute" in blob, "spec_file is resolved by the server, not the caller"
        assert "not necessarily the proof you" in blob, "recovery can replace a submitted proof"

    def test_batching_semantics_are_stated_not_inferred(self):
        text = guide.topic("formalize")
        assert "own namespace" in text, "callers defensively namespaced work build_batch already does"
        assert "rebased" in text, "line numbers are proof-relative, which is not obvious"

    def test_the_schema_lists_every_field_the_loader_requires(self):
        from formal.specs import REQUIRED

        documented = guide.index()["spec_file"]["schema"]["properties"][0]
        assert set(REQUIRED) <= set(documented)

    def test_the_index_stays_small(self):
        """Every agent pays for this one, whether or not it goes further."""
        assert len(json.dumps(guide.index())) < 6000


class TestTopics:
    @pytest.mark.parametrize("name", ["extract", "formalize", "tactics"])
    def test_a_topic_renders(self, name):
        assert len(guide.topic(name)) > 500

    @pytest.mark.parametrize("name", ["extract", "formalize", "tactics"])
    def test_no_placeholder_survives_rendering(self, name):
        """An unsubstituted {function_code} is something an agent will try to reason about."""
        leftover = PLACEHOLDER.findall(guide.topic(name))
        assert leftover == []

    @pytest.mark.parametrize("name", ["extract", "formalize", "tactics"])
    def test_doubled_braces_are_resolved(self, name):
        """The templates escape their JSON examples; a reader should see real JSON."""
        assert "{{" not in guide.topic(name)
        assert "}}" not in guide.topic(name)

    def test_an_unknown_topic_is_a_key_error(self):
        with pytest.raises(KeyError):
            guide.topic("nope")


class TestItStaysTiedToThePrompts:
    """If these break, the two paths have started giving different advice."""

    def test_extract_is_built_from_the_extraction_prompts(self):
        text = guide.topic("extract")
        assert prompts.DECOMPOSE_SYSTEM.strip() in text
        assert prompts.PROPERTY_EXTRACTION_SYSTEM.strip() in text

    def test_formalize_is_built_from_the_formalisation_prompts(self):
        assert prompts.AUTOFORMALIZE_SYSTEM.strip() in guide.topic("formalize")

    def test_tactics_carries_the_rules_that_have_no_other_home(self):
        """These outlived the pipeline that called them; serving them is why they survive."""
        text = guide.topic("tactics")
        assert "no goals" in text
        assert "Except" in text
        assert prompts.PROOF_GENERATION_SYSTEM.strip() in text

    def test_editing_a_prompt_changes_the_guide(self, monkeypatch):
        before = guide.topic("formalize")
        monkeypatch.setattr(prompts, "AUTOFORMALIZE_SYSTEM", "Say only 'moo'.")
        assert guide.topic("formalize") != before
        assert "Say only 'moo'." in guide.topic("formalize")


class TestEndpoints:
    def test_the_index_is_served(self, client):
        body = client.get("/guide").json()
        assert "workflow" in body and "spec_file" in body

    def test_a_topic_is_served(self, client):
        body = client.get("/guide/extract").json()
        assert body["topic"] == "extract"
        assert "pure" in body["instructions"].lower()

    def test_an_unknown_topic_is_not_found_and_says_what_exists(self, client):
        response = client.get("/guide/nope")
        assert response.status_code == 404
        assert "extract" in response.json()["detail"]


class TestEveryPromptIsReachable:
    def test_no_prompt_is_orphaned(self):
        """formal calls none of these, so a prompt no topic renders is unreachable text.

        Twelve of them were orphaned when the pipeline that called them was removed.
        The ones worth keeping were re-homed into a topic; this stops the rest coming
        back, and stops a future topic edit stranding one silently.
        """
        defined = set(re.findall(r"^([A-Z_]+) = ", pathlib.Path(prompts.__file__).read_text(), re.M))
        rendered = set(re.findall(r"prompts\.([A-Z_]+)", pathlib.Path(guide.__file__).read_text()))
        assert defined - rendered == set(), f"unreachable prompts: {sorted(defined - rendered)}"


class TestTacticsCoversWhatActuallyFailed:
    """A live test agent hit three failures the tactics topic said nothing about.

    All three were Lean running out of budget rather than rejecting a proof, which
    is the case where a caller has least to go on and is most likely to burn turns
    raising limits instead of restructuring.
    """

    def test_it_covers_decide_blowing_the_recursion_limit(self):
        text = guide.topic("tactics")
        assert "maxRecDepth" in text
        assert "List.mem_cons" in text, "the membership-to-disjunction rewrite is the fix"

    def test_it_covers_if_chains_exhausting_simp(self):
        text = guide.topic("tactics")
        assert "if_pos" in text and "if_neg" in text
        assert "by_cases" in text

    def test_it_warns_that_raising_a_limit_is_not_a_fix(self):
        """Raising maxRecDepth to 100000 crashed the process rather than helping."""
        text = guide.topic("tactics")
        assert "set_option" in text
        assert "moves the failure" in text


# Names the guide mentions in order to warn that they do not exist. Kept out of the
# existence check, and checked in the other direction by the test below.
CITED_AS_ABSENT = {
    "List.append_inj_iff",
    "List.append_left_cancel",
    "List.append_right_cancel",
    "List.isPrefixOf_append_left",
    "List.length_eq_one",
}


class TestDocumentedLemmasExist:
    """The guide tells callers not to guess lemma names. It has to hold itself to that.

    The filter family went in because a live agent needed it and found nothing; one
    name it would have been natural to add, List.length_filter, does not exist in this
    Mathlib at all. A Mathlib bump can invalidate any of these silently.

    Opt-in: FORMAL_LEAN_TESTS=1 uv run pytest -k DocumentedLemmas  (runs Lean, ~5s)
    """

    def test_every_lemma_named_in_the_guide_elaborates(self):
        import os

        if os.getenv("FORMAL_LEAN_TESTS") != "1":
            pytest.skip("set FORMAL_LEAN_TESTS=1 to check lemma names against Lean")

        from formal.lean_verifier import verify

        text = "".join(guide.topic(t) for t in guide.TOPICS)
        names = set(re.findall(r"List\.[A-Za-z_][A-Za-z0-9_']*[?!]?", text)) - CITED_AS_ABSENT
        assert names, "no lemma names found — the extraction regex has drifted"

        result = verify("import Mathlib\n\n" + "\n".join(f"#check @{n}" for n in sorted(names)))
        missing = [e.get("data", "").replace("\n", " ") for e in result.errors]
        assert result.success, "guide recommends lemmas that do not exist: " + "; ".join(missing)

    def test_the_names_cited_as_absent_are_still_absent(self):
        """If Mathlib adds one, the guide's warning about it has become wrong."""
        import os

        if os.getenv("FORMAL_LEAN_TESTS") != "1":
            pytest.skip("set FORMAL_LEAN_TESTS=1 to check lemma names against Lean")

        from formal.lean_verifier import verify

        for name in sorted(CITED_AS_ABSENT):
            result = verify(f"import Mathlib\n\n#check @{name}")
            assert not result.success, f"{name} now exists — the guide still warns against it"


class TestExtractReadsAsInstructions:
    """It was a prompt template: placeholders for a caller that no longer exists, and an
    output schema with fields the spec file has no home for. Two agents worked around it."""

    def test_no_input_placeholder_survives(self):
        assert not re.findall(r"<the [^>]+>", guide.topic("extract"))

    def test_the_dead_output_schema_is_gone(self):
        text = guide.topic("extract")
        assert "unverifiable_reason" not in text
        assert "verifiable=" not in text

    def test_every_kind_the_schema_allows_is_defined(self):
        """The six values were listed as an enum and never explained."""
        text = guide.topic("extract")
        for kind in ("bound", "identity", "monotonicity", "commutativity", "idempotency", "invariant"):
            assert re.search(rf"^  {kind}\s+\S", text, re.M), f"{kind} is listed but not defined"

    def test_staleness_matching_is_documented(self):
        """A caller guessed substring semantics and had no way to confirm it."""
        assert "trailing whitespace ignored" in guide.topic("extract")


class TestNestedCaseAnalysis:
    def test_the_nested_pair_case_is_covered(self):
        """Flat membership was documented; a table of pairs blew the limit anyway."""
        text = guide.topic("tactics")
        assert "table of pairs" in text
        assert "List.not_mem_nil" in text

    def test_the_two_nil_lemmas_are_distinguished(self):
        """They are not interchangeable and the wrong one costs a retry."""
        text = guide.topic("tactics")
        assert "List.mem_nil_iff" in text and "List.not_mem_nil" in text


class TestSecondRunGuidance:
    """Run 3 arrived at a directory that already had a spec file. The workflow only said
    to write one, never what to do when one exists — and regenerating it discards every
    cached proof, which is the whole point of committing it."""

    def test_it_says_to_reuse_an_existing_spec_file(self):
        steps = " ".join(guide.index()["workflow"])
        assert "already exists" in steps
        assert "do not replace it" in steps

    def test_the_asymmetric_response_shapes_are_called_out(self):
        """cached is a list of objects, work a list of strings; a caller coded the wrong one."""
        steps = " ".join(guide.index()["workflow"])
        assert "bare id strings" in steps

    def test_the_schema_endpoint_is_advertised(self):
        assert "openapi.json" in json.dumps(guide.index())

    def test_a_counterexample_has_a_kind(self):
        """Two proven collisions had no honest kind; the caller filed them as identity."""
        assert "counterexample" in guide.topic("extract")


class TestKindsHaveOneDefinition:
    """kind was enumerated in two places and they disagreed after `counterexample` was
    added to one of them. kind is in the cache key, so a caller guessing the wrong value
    silently loses its hits."""

    def test_the_schema_and_the_instructions_list_the_same_kinds(self):
        listed = json.dumps(guide.index())
        explained = guide.topic("extract")
        for kind in guide.KINDS:
            assert kind in listed, f"{kind} explained but not offered in the schema"
            assert kind in explained, f"{kind} offered but never explained"

    def test_no_kind_is_offered_without_being_explained(self):
        for kind, meaning in guide.KINDS.items():
            assert meaning.strip(), f"{kind} has no explanation"

    def test_the_block_actually_renders(self):
        assert "%%KINDS%%" not in guide.topic("extract")


class TestGuidanceRunFourNeeded:
    def test_the_property_budget_does_not_contradict_itself(self):
        """ "2-5 per function, at most 10 total" is unsatisfiable past two functions."""
        assert "at most 10" not in guide.topic("extract")

    def test_element_arithmetic_is_not_forced_into_List_Char(self):
        """The List Char rule exists because Lean's String is unusable, not because every
        sequence is text — a caller doing byte arithmetic had to deviate silently."""
        text = guide.topic("extract")
        assert "List Nat" in text
        assert "what the code does with an element" in text, "the rule must key on behaviour"

    def test_the_id_is_not_claimed_to_matter_to_the_cache(self):
        assert "renaming keeps the cached proof" in json.dumps(guide.index())

    def test_the_proof_field_is_named(self):
        assert "lean_code" in json.dumps(guide.index())

    def test_the_workflow_says_to_read_ahead_before_committing(self):
        """What is provable decides what belongs in the spec, and the spec is committed."""
        assert "before you commit" in " ".join(guide.index()["workflow"])


class TestTheGuideNamesNoLanguage:
    """The guide is served to an agent working in whatever language the caller uses.

    Java-specific examples were removed once; a byte-array rule naming three languages'
    type spellings went in hours later. State rules by what the code does, not by what
    one language calls the type.
    """

    SPELLINGS = [
        "[]const u8",
        "Vec<u8>",
        "byte[]",
        "[]byte",
        "unsigned char",
        "std::",
        "JVM",
        "getType",
        "PLUS.",
        "BigDecimal",
        "__init__",
        "nullptr",
    ]

    def test_no_topic_names_a_language_specific_type_or_idiom(self):
        served = "".join(guide.topic(t) for t in guide.TOPICS)
        found = [s for s in self.SPELLINGS if s in served]
        assert found == [], f"language-specific spellings in the guide: {found}"

    def test_the_index_names_none_either(self):
        served = json.dumps(guide.index())
        found = [s for s in self.SPELLINGS if s in served]
        assert found == [], f"language-specific spellings in the index: {found}"
