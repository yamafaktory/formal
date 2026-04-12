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
    from formal.property_verifier import PropertyResult

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
        k1 = cache_key("code", "desc", "kind", "formal", [], [])
        k2 = cache_key("code", "desc", "kind", "formal", [], [])
        assert k1 == k2

    def test_different_code_different_key(self):
        k1 = cache_key("code_a", "desc", "kind", "formal", [], [])
        k2 = cache_key("code_b", "desc", "kind", "formal", [], [])
        assert k1 != k2

    def test_different_preconditions_different_key(self):
        k1 = cache_key("code", "desc", "kind", "formal", ["n > 0"], [])
        k2 = cache_key("code", "desc", "kind", "formal", [], [])
        assert k1 != k2

    def test_different_assumptions_different_key(self):
        k1 = cache_key("code", "desc", "kind", "formal", [], ["floats as rationals"])
        k2 = cache_key("code", "desc", "kind", "formal", [], [])
        assert k1 != k2

    def test_precondition_order_matters(self):
        k1 = cache_key("code", "desc", "kind", "formal", ["a", "b"], [])
        k2 = cache_key("code", "desc", "kind", "formal", ["b", "a"], [])
        assert k1 != k2

    def test_returns_hex_string(self):
        k = cache_key("code", "desc", "kind", "formal", [], [])
        assert len(k) == 64
        assert all(c in "0123456789abcdef" for c in k)


# ── save / load ───────────────────────────────────────────────────────────────


class TestSaveLoad:
    def test_roundtrip(self, tmp_cache):
        result = make_result()
        key = cache_key("code", "desc", "kind", "formal", [], [])
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

    def test_preconditions_and_assumptions_survive_roundtrip(self, tmp_cache):
        result = make_result(preconditions=["n > 0"], assumptions=["floats as rationals"])
        key = cache_key("code", "desc", "kind", "formal", ["n > 0"], ["floats as rationals"])
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
        key = cache_key("code", "desc", "kind", "formal", [], [])
        save(key, result)
        # Save again to trigger eviction check
        save(key, result)
        assert load(key) is not None

    def test_expired_entry_evicted(self, tmp_cache, monkeypatch):
        import formal.proof_cache as pc

        monkeypatch.setattr(pc, "_CACHE_TTL_DAYS", 7)
        result = make_result()
        key = cache_key("code", "desc", "kind", "formal", [], [])

        # Write a cache file and backdate its mtime to 8 days ago
        save(key, result)
        cache_file = tmp_cache / f"{key}.json"
        old_time = time.time() - 8 * 86400
        import os

        os.utime(cache_file, (old_time, old_time))

        # Saving a second entry triggers eviction
        key2 = cache_key("code2", "desc", "kind", "formal", [], [])
        save(key2, make_result(property_id="prop_2"))

        assert not cache_file.exists()

    def test_large_ttl_does_not_evict_old_entry(self, tmp_cache, monkeypatch):
        import os

        import formal.proof_cache as pc

        monkeypatch.setattr(pc, "_CACHE_TTL_DAYS", 365)
        result = make_result()
        key = cache_key("code", "desc", "kind", "formal", [], [])
        save(key, result)

        # Backdate the file to 8 days ago — still within 365-day TTL
        cache_file = tmp_cache / f"{key}.json"
        old_time = time.time() - 8 * 86400
        os.utime(cache_file, (old_time, old_time))

        # Saving a second entry triggers eviction — 8-day-old file should survive
        key2 = cache_key("code2", "desc", "kind", "formal", [], [])
        save(key2, make_result(property_id="prop_2"))

        assert cache_file.exists()
