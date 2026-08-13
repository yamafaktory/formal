"""Every hint pinned to its text, and every rule in the table reached by a sample.

The hints were a 434-line `if ... in data` chain — 16% of the codebase and the
single largest thing a rewrite has to reproduce. Unit tests covered the branches
someone thought to write one for; this covers all of them. The fixture was built
by walking the chain until line and branch coverage of the function were complete,
so a refactor that drops, reorders or subtly rewords a rule fails here rather than
in front of an agent trying to fix a proof.

Now that the rules are data, the corpus does a second job: data rots in a way code
does not, because a rule that can never match is not dead code anyone will notice.
Every rule must be reached.

The hints are recorded as-is, not as assertions about what they ought to say. The
question this answers is only "does it still say the same thing".
"""

import json
import pathlib

import pytest

from formal import hints
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
        assert len(corpus) == 49

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
        ["function_expected_field", "function_expected_field_word"],
        ["guessed_lemma", "unknown_identifier_unquoted"],
    ]

    def test_only_the_known_groups_share_advice(self, corpus):
        by_hint: dict[str, list[str]] = {}
        for name, case in corpus.items():
            by_hint.setdefault(case["hint"], []).append(name)
        shared = sorted(sorted(names) for names in by_hint.values() if len(names) > 1)
        assert shared == self.EXPECTED_GROUPS


class TestNoRuleIsUnreachable:
    """A rule the corpus cannot reach is either dead or shadowed by an earlier one.

    Both are silent: the table still loads, and the only symptom is advice nobody
    ever gets. Finding one means either writing the sample that reaches it or
    deleting the rule.
    """

    def _rule_ids(self, rules) -> set[str]:
        found: set[str] = set()
        for rule in rules:
            found.add(rule["id"])
            found |= self._rule_ids(rule.get("sub", []))
        return found

    def test_every_rule_answers_at_least_one_sample(self, corpus, monkeypatch):
        fired: set[str] = set()
        matches = hints._matches

        def record(rule, data):
            if matches(rule, data):
                fired.add(rule["id"])
                return True
            return False

        monkeypatch.setattr(hints, "_matches", record)
        for case in corpus.values():
            if case["error"] is not None:
                hints.hint_for(case["error"])

        assert self._rule_ids(hints.table()["rule"]) - fired == set()
