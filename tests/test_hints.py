"""The matcher and the shape of the table it reads.

tests/test_hint_corpus.py answers "does it still say the same thing". This
answers the questions that only arise once the rules are data: that a malformed
table is refused at load rather than silently answering nothing, and that the
matcher's fall-through is the one the old nested `if` chain had.
"""

import pytest

from formal import hints
from formal.hints import HintTableError, _answer, _matches, hint_for, table


class TestMatching:
    def test_all_requires_every_term(self):
        rule = {"id": "r", "all": ["alpha", "beta"]}
        assert _matches(rule, "alpha and beta")
        assert not _matches(rule, "alpha only")

    def test_any_is_satisfied_by_one_group(self):
        rule = {"id": "r", "any": [["alpha"], ["beta"]]}
        assert _matches(rule, "beta")
        assert not _matches(rule, "gamma")

    def test_a_group_is_itself_a_conjunction(self):
        """`zipWith or sum or (* and =)` is the shape that forced groups to be lists."""
        rule = {"id": "r", "any": [["zipWith"], ["*", "="]]}
        assert _matches(rule, "zipWith")
        assert _matches(rule, "a * b = c")
        assert not _matches(rule, "a * b")

    def test_all_and_any_are_combined(self):
        rule = {"id": "r", "all": ["unsolved goals"], "any": [["isPrefixOf"], ["startsWith"]]}
        assert _matches(rule, "unsolved goals: startsWith")
        assert not _matches(rule, "unsolved goals only")
        assert not _matches(rule, "startsWith only")

    def test_lower_folds_the_subject_not_the_terms(self):
        assert _matches({"id": "r", "lower": True, "all": ["unknown identifier"]}, "Unknown Identifier `x`")
        assert not _matches({"id": "r", "all": ["unknown identifier"]}, "Unknown Identifier `x`")

    def test_equals_is_exact_and_ignores_containment(self):
        rule = {"id": "r", "equals": "timeout"}
        assert _matches(rule, "timeout")
        assert not _matches(rule, "the proof hit a timeout")

    def test_a_rule_with_no_conditions_matches_anything(self):
        """How `tactic_failed` gets to run its pattern over every error."""
        assert _matches({"id": "r"}, "")


class TestFallThrough:
    def test_a_handler_that_declines_hands_back_to_the_next_sibling(self):
        loaded = {"handler": {"tactic_failed": table()["handler"]["tactic_failed"]}, "text": {}}
        rule = {
            "id": "parent",
            "hint": "parent answer",
            "sub": [
                {"id": "declines", "handler": "tactic_failed"},
                {"id": "answers", "hint": "sibling answer"},
            ],
        }
        assert _answer(rule, "nothing a tactic pattern will match", loaded) == "sibling answer"

    def test_a_parent_answers_when_no_sub_does(self):
        rule = {"id": "parent", "hint": "parent answer", "sub": [{"id": "s", "all": ["nope"], "hint": "sub"}]}
        assert _answer(rule, "anything", {"handler": {}, "text": {}}) == "parent answer"

    def test_a_top_level_rule_producing_nothing_does_not_stop_the_search(self):
        """`tactic_failed` matches every error but answers few — the rest must reach the fallback."""
        assert hint_for("an error with no tactic in it") == table()["fallback"]


class TestTheTableIsUsable:
    def test_it_loads(self):
        assert table()["version"] == hints.SCHEMA_VERSION

    def test_every_rule_has_an_id(self):
        def walk(rules):
            for rule in rules:
                assert rule.get("id"), rule
                walk(rule.get("sub", []))

        walk(table()["rule"])

    def test_no_hint_is_blank(self):
        def walk(rules):
            for rule in rules:
                if "hint" in rule:
                    assert rule["hint"].strip(), rule["id"]
                walk(rule.get("sub", []))

        walk(table()["rule"])

    def test_every_configured_handler_is_used_by_a_rule(self):
        used = set()

        def walk(rules):
            for rule in rules:
                if "handler" in rule:
                    used.add(rule["handler"])
                walk(rule.get("sub", []))

        walk(table()["rule"])
        assert set(table()["handler"]) == used

    def test_every_named_text_is_referenced(self):
        referenced = set()

        def walk(rules):
            for rule in rules:
                if "hint_ref" in rule:
                    referenced.add(rule["hint_ref"])
                walk(rule.get("sub", []))

        walk(table()["rule"])
        assert set(table()["text"]) == referenced

    def test_the_specific_omega_rule_is_tried_before_the_general_one(self):
        """Order is the semantics, and these two are the pair that proves it."""
        ids = [rule["id"] for rule in table()["rule"]]
        assert ids.index("omega_on_a_string_literal") < ids.index("omega_beyond_linear_arithmetic")


class TestAMalformedTableIsRefused:
    def _validate(self, table_data):
        with pytest.raises(HintTableError) as caught:
            hints._validate(table_data)
        return str(caught.value)

    def test_a_future_version_is_not_guessed_at(self):
        assert "version" in self._validate({"version": 99, "fallback": "f", "rule": [{"id": "r", "hint": "h"}]})

    def test_a_table_without_a_fallback_is_refused(self):
        assert "fallback" in self._validate({"version": 1, "rule": [{"id": "r", "hint": "h"}]})

    def test_a_table_without_rules_is_refused(self):
        assert "no rules" in self._validate({"version": 1, "fallback": "f", "rule": []})

    def test_a_rule_that_cannot_answer_is_refused(self):
        assert "no answer" in self._validate({"version": 1, "fallback": "f", "rule": [{"id": "r", "all": ["x"]}]})

    def test_a_rule_answering_two_ways_is_refused(self):
        rule = {"id": "r", "hint": "h", "handler": "tactic_failed"}
        assert "more than one" in self._validate({"version": 1, "fallback": "f", "rule": [rule]})

    def test_an_unknown_handler_is_refused(self):
        rule = {"id": "r", "handler": "no_such_handler"}
        assert "unknown handler" in self._validate({"version": 1, "fallback": "f", "rule": [rule]})

    def test_a_handler_with_no_configuration_is_refused(self):
        data = {"version": 1, "fallback": "f", "handler": {}, "rule": [{"id": "r", "handler": "tactic_failed"}]}
        assert "no configuration" in self._validate(data)

    def test_a_dangling_text_reference_is_refused(self):
        rule = {"id": "r", "hint_ref": "nowhere"}
        assert "unknown text" in self._validate({"version": 1, "fallback": "f", "text": {}, "rule": [rule]})

    def test_a_duplicate_id_is_refused(self):
        rules = [{"id": "r", "hint": "a"}, {"id": "r", "hint": "b"}]
        assert "duplicate" in self._validate({"version": 1, "fallback": "f", "rule": rules})

    def test_a_sub_rule_is_validated_too(self):
        rule = {"id": "parent", "hint": "h", "sub": [{"id": "child", "handler": "nope"}]}
        assert "parent/child" in self._validate({"version": 1, "fallback": "f", "rule": [rule]})
