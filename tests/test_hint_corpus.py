"""Every hint branch pinned to its current text, before the chain becomes data.

`hint_for_error` is 434 lines of `if ... in data` — 16% of the codebase and the
single largest thing a rewrite has to reproduce. Unit tests covered the branches
someone thought to write one for; this covers all of them. The fixture was built
by walking the chain until line and branch coverage of the function were complete,
so a refactor that drops, reorders or subtly rewords a branch fails here rather
than in front of an agent trying to fix a proof.

The hints are recorded as-is, not as assertions about what they ought to say. The
question this answers is only "does it still say the same thing".
"""

import json
import pathlib

import pytest

from formal.lean_verifier import LeanResult

FIXTURE = pathlib.Path(__file__).parent / "fixtures" / "hint_corpus.json"
FALLBACK = "unmatched"


@pytest.fixture(scope="module")
def corpus():
    return json.loads(FIXTURE.read_text())


def _hint(error: str | None) -> str:
    errors = [] if error is None else [{"data": error}]
    return LeanResult(success=False, output=error or "", errors=errors).hint_for_error()


class TestFrozenHints:
    def test_the_corpus_is_the_size_it_was_measured_at(self, corpus):
        assert len(corpus) == 48

    def test_every_recorded_error_still_produces_its_recorded_hint(self, corpus):
        changed = {
            name: (case["hint"], _hint(case["error"]))
            for name, case in corpus.items()
            if _hint(case["error"]) != case["hint"]
        }
        assert changed == {}

    def test_only_the_fallback_sample_falls_through(self, corpus):
        """A new branch inserted above an old one would silently shadow it."""
        fell_through = [name for name, case in corpus.items() if case["hint"] == corpus[FALLBACK]["hint"]]
        assert fell_through == [FALLBACK]

    def test_no_hint_is_empty_except_for_no_errors(self, corpus):
        assert [name for name, case in corpus.items() if not case["hint"] and case["error"] is not None] == []


class TestTheCorpusStillDiscriminates:
    """Every other sample must reach a branch of its own.

    Three groups legitimately share an answer: four different errors are all the
    same string-prefix limitation, and two branches have an internal fallback for
    the shape they could not parse. Anything else sharing a hint means a sample is
    being answered by the wrong branch, which is how a reordering hides a bug.
    """

    EXPECTED_GROUPS = [
        ["app_mismatch_bare", "app_mismatch_option_same_inner"],
        ["forward_pattern", "free_vars_string", "prefix_not_defeq", "prefix_unsolved_append"],
        ["guessed_lemma", "unknown_identifier_unquoted"],
    ]

    def test_only_the_known_groups_share_advice(self, corpus):
        by_hint: dict[str, list[str]] = {}
        for name, case in corpus.items():
            by_hint.setdefault(case["hint"], []).append(name)
        shared = sorted(sorted(names) for names in by_hint.values() if len(names) > 1)
        assert shared == self.EXPECTED_GROUPS
