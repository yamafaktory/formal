"""Tests for proof_cache — key determinism, save/load, TTL eviction."""

import time

import pytest

from formal.proof_cache import cache_key, load, save

# ── Fixtures ──────────────────────────────────────────────────────────────────


@pytest.fixture
def tmp_cache(tmp_path, monkeypatch):
    """Redirect cache writes to a temp directory."""
    import formal.proof_cache as pc

    monkeypatch.setattr(pc, "_CACHE_DIR", tmp_path)
    return tmp_path


def make_result(**kwargs):
    """Build a minimal PropertyResult-like object via the real dataclass."""
    from formal.results import PropertyResult

    defaults = dict(
        property_id="prop_1",
        description="output is sorted",
        kind="invariant",
        function="sort_list",
        verified=True,
        lean_code="theorem foo : True := trivial",
        lean_output="",
        retries=0,
        reason="",
        status="verified",
        preconditions=[],
        assumptions=[],
    )
    return PropertyResult(**{**defaults, **kwargs})


# ── cache_key ─────────────────────────────────────────────────────────────────


class TestCacheKey:
    def test_same_inputs_same_key(self):
        assert cache_key("code", "kind", "formal") == cache_key("code", "kind", "formal")

    def test_different_code_different_key(self):
        assert cache_key("code_a", "kind", "formal") != cache_key("code_b", "kind", "formal")

    def test_different_kind_different_key(self):
        assert cache_key("code", "bound", "formal") != cache_key("code", "identity", "formal")

    def test_different_formal_different_key(self):
        assert cache_key("code", "kind", "f x = x") != cache_key("code", "kind", "f x = y")

    def test_returns_hex_string(self):
        k = cache_key("code", "kind", "formal")
        assert len(k) == 64
        assert all(c in "0123456789abcdef" for c in k)


class TestKeySurvivesParaphrase:
    """The key identifies what is proved. Prose describing it is free to vary.

    A fixed prompt at temperature 0 reproduced its own wording, so mixing prose
    into the key was harmless. An agent paraphrases every run, and each paraphrase
    was a fresh key and a re-proof of something already proved.
    """

    def test_operator_spelling_does_not_split_the_key(self):
        assert cache_key("code", "kind", "∀ x, p x → q x") == cache_key("code", "kind", "forall x, p x -> q x")

    def test_spacing_does_not_split_the_key(self):
        assert cache_key("code", "kind", "f(f(x)) == f(x)") == cache_key("code", "kind", "f( f( x ) )  ==  f(x)")

    def test_kind_casing_does_not_split_the_key(self):
        assert cache_key("code", "Idempotence", "formal") == cache_key("code", "idempotence", "formal")

    def test_trailing_whitespace_in_code_does_not_split_the_key(self):
        assert cache_key("def f():\n    return 1", "kind", "formal") == cache_key(
            "\ndef f():   \n    return 1  \n", "kind", "formal"
        )

    def test_indentation_still_splits_the_key(self):
        """Indentation is meaning in Python — two bodies are two functions."""
        assert cache_key("def f():\n  return 1", "kind", "formal") != cache_key(
            "def f():\n      return 1", "kind", "formal"
        )


# ── save / load ───────────────────────────────────────────────────────────────


class TestSaveLoad:
    def test_roundtrip(self, tmp_cache):
        result = make_result()
        key = cache_key("code", "kind", "formal")
        save(key, result)
        loaded = load(key)
        assert loaded is not None
        assert loaded.property_id == result.property_id
        assert loaded.verified == result.verified

    def test_load_missing_returns_none(self, tmp_cache):
        assert load("nonexistent_key") is None

    def test_load_corrupt_returns_none(self, tmp_cache):
        path = tmp_cache / "bad.json"
        path.write_text("not valid json{{{")
        assert load("bad") is None

    def test_loaded_result_has_cached_false(self, tmp_cache):
        result = make_result()
        key = cache_key("code", "kind", "formal")
        save(key, result)
        loaded = load(key)
        # Saved result has cached=False; caller marks it True after loading
        assert loaded.cached is False

    def test_preconditions_and_assumptions_survive_roundtrip(self, tmp_cache):
        result = make_result(preconditions=["n > 0"], assumptions=["floats as rationals"])
        key = cache_key("code", "kind", "formal")
        save(key, result)
        loaded = load(key)
        assert loaded.preconditions == ["n > 0"]
        assert loaded.assumptions == ["floats as rationals"]


# ── TTL eviction ──────────────────────────────────────────────────────────────


class TestTTLEviction:
    def test_fresh_entry_not_evicted(self, tmp_cache, monkeypatch):
        import formal.proof_cache as pc

        monkeypatch.setattr(pc, "_CACHE_TTL_DAYS", 7)
        result = make_result()
        key = cache_key("code", "kind", "formal")
        save(key, result)
        # Save again to trigger eviction check
        save(key, result)
        assert load(key) is not None

    def test_expired_entry_evicted(self, tmp_cache, monkeypatch):
        import formal.proof_cache as pc

        monkeypatch.setattr(pc, "_CACHE_TTL_DAYS", 7)
        result = make_result()
        key = cache_key("code", "kind", "formal")

        # Write a cache file and backdate its mtime to 8 days ago
        save(key, result)
        cache_file = tmp_cache / f"{key}.json"
        old_time = time.time() - 8 * 86400
        import os

        os.utime(cache_file, (old_time, old_time))

        # Saving a second entry triggers eviction
        key2 = cache_key("code2", "kind", "formal")
        save(key2, make_result(property_id="prop_2"))

        assert not cache_file.exists()

    def test_large_ttl_does_not_evict_old_entry(self, tmp_cache, monkeypatch):
        import os

        import formal.proof_cache as pc

        monkeypatch.setattr(pc, "_CACHE_TTL_DAYS", 365)
        result = make_result()
        key = cache_key("code", "kind", "formal")
        save(key, result)

        # Backdate the file to 8 days ago — still within 365-day TTL
        cache_file = tmp_cache / f"{key}.json"
        old_time = time.time() - 8 * 86400
        os.utime(cache_file, (old_time, old_time))

        # Saving a second entry triggers eviction — 8-day-old file should survive
        key2 = cache_key("code2", "kind", "formal")
        save(key2, make_result(property_id="prop_2"))

        assert cache_file.exists()


class TestSaveFailuresAreNonFatal:
    """A cache write must never change a verification verdict."""

    def test_unwritable_directory_does_not_raise(self, tmp_path, monkeypatch):
        import formal.proof_cache as pc

        locked = tmp_path / "locked"
        locked.mkdir(mode=0o500)
        monkeypatch.setattr(pc, "_CACHE_DIR", locked / "cache")

        key = cache_key("code", "kind", "formal")
        save(key, make_result())

    def test_unwritable_file_does_not_raise(self, tmp_cache, monkeypatch):
        key = cache_key("code", "kind", "formal")
        blocker = tmp_cache / f"{key}.json"
        blocker.mkdir()

        save(key, make_result())

    def test_a_healthy_cache_still_writes(self, tmp_cache):
        key = cache_key("code", "kind", "formal")
        save(key, make_result())

        assert (tmp_cache / f"{key}.json").is_file()
        assert load(key) is not None
