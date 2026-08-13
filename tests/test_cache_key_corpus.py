"""The cache key checked against real extracted properties, not invented ones.

tests/fixtures/extracted_properties.json holds the 148 properties formal produced
while checking its own source — 76 functions across 5 kinds. The key dropped the
description, preconditions and assumptions so that a paraphrase stops forcing a
re-proof; what has to hold is that dropping them does not make two genuinely
different properties share an entry. Invented examples cannot answer that. This
corpus can, and it is the evidence the change was made on.
"""

import json
import pathlib

import pytest

from formal.proof_cache import cache_key, normalise_formal

FIXTURE = pathlib.Path(__file__).parent / "fixtures" / "extracted_properties.json"
GOLDEN = pathlib.Path(__file__).parent / "fixtures" / "cache_keys.json"


@pytest.fixture(scope="module")
def corpus():
    return json.loads(FIXTURE.read_text())


@pytest.fixture(scope="module")
def golden():
    return json.loads(GOLDEN.read_text())


def _key(prop):
    return cache_key(prop["function"], prop["kind"], prop["formal"])


class TestNoCollisions:
    def test_the_corpus_is_the_size_it_was_measured_at(self, corpus):
        assert len(corpus) == 148

    def test_every_property_gets_its_own_key(self, corpus):
        keys = {}
        for prop in corpus:
            key = _key(prop)
            clash = keys.get(key)
            assert clash is None, f"{prop['function']}/{prop['kind']} collides with {clash['function']}: {clash}"
            keys[key] = prop
        assert len(keys) == len(corpus)

    def test_function_and_kind_alone_would_collide(self, corpus):
        """Why `formal` cannot be dropped as well: 76 functions, 5 kinds, 148 properties."""
        coarse = {(p["function"], p["kind"]) for p in corpus}
        assert len(coarse) < len(corpus)

    def test_no_property_has_an_empty_formal_statement(self, corpus):
        """An empty one would key on function and kind alone, which collides."""
        assert [p["function"] for p in corpus if not p["formal"].strip()] == []


class TestNormalisationIsStableOverTheCorpus:
    def test_normalising_twice_changes_nothing(self, corpus):
        for prop in corpus:
            once = normalise_formal(prop["formal"])
            assert normalise_formal(once) == once

    def test_normalisation_never_empties_a_statement(self, corpus):
        assert all(normalise_formal(p["formal"]) for p in corpus)

    def test_unicode_and_ascii_spellings_agree_across_the_corpus(self, corpus):
        """Rewriting each statement the way another writer might must not move its key."""
        # Longest first, or "->" mangles "<->" into "<→" before it can be matched.
        swaps = [("<->", "↔"), ("->", "→"), ("/\\", "∧"), ("\\/", "∨"), ("forall", "∀"), ("exists", "∃")]
        for prop in corpus:
            rewritten = prop["formal"]
            for ascii_form, symbol in swaps:
                rewritten = rewritten.replace(ascii_form, symbol)
            assert _key({**prop, "formal": rewritten}) == _key(prop)

    def test_reindenting_a_statement_does_not_move_its_key(self, corpus):
        for prop in corpus:
            spaced = prop["formal"].replace(",", " ,  ").replace("(", " ( ")
            assert _key({**prop, "formal": spaced}) == _key(prop)


class TestTheKeysThemselvesAreFrozen:
    """The exact digests, so a reimplementation can be checked against them.

    Everything above says the key discriminates. This says what the key *is*.
    A rewrite that gets the framing, the operator table or the ordering subtly
    wrong still passes every property above and silently invalidates every
    cached proof in existence — the cost is not wrong answers, it is that no
    entry is ever found again. There is no way to notice that from behaviour.
    """

    def test_the_corpus_keys_have_not_moved(self, golden):
        moved = [entry["inputs"] for entry in golden["corpus"] if cache_key(*entry["inputs"]) != entry["key"]]
        assert moved == []

    def test_the_crafted_keys_have_not_moved(self, golden):
        moved = [entry["name"] for entry in golden["crafted"] if cache_key(*entry["inputs"]) != entry["key"]]
        assert moved == []

    def test_the_golden_file_covers_the_whole_corpus(self, corpus, golden):
        assert len(golden["corpus"]) == len(corpus)

    def _keys(self, golden):
        return {entry["name"]: entry["key"] for entry in golden["crafted"]}

    def test_spelling_an_operator_either_way_gives_one_key(self, golden):
        keys = self._keys(golden)
        assert keys["ascii and unicode operators agree"] == keys["the same statement written in symbols"]
        assert keys["iff is matched before the arrow inside it"] == keys["iff written as a symbol"]

    def test_a_word_operator_is_not_matched_inside_an_identifier(self, golden):
        """`a in b` and `ainb` collapsed together once; they must not again."""
        keys = self._keys(golden)
        assert keys["word operators only count on a boundary"] != keys["letters that merely spell one do not"]

    def test_no_field_can_imitate_the_boundary_of_another(self, golden):
        keys = self._keys(golden)
        assert keys["fields cannot imitate each other's boundary"] != keys["the other side of that boundary"]

    def test_indentation_survives_but_trailing_space_does_not(self, golden):
        keys = self._keys(golden)
        assert keys["indentation is significant in the code"] == keys["but trailing whitespace in the code is not"]
