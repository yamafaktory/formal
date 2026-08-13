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


@pytest.fixture(scope="module")
def corpus():
    return json.loads(FIXTURE.read_text())


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
