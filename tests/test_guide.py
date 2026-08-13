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
