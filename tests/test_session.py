"""Tests for proof sessions — the state that keeps a retry from resending everything.

The load-bearing behaviours: metadata is registered once, the cache is consulted
before any Lean runs, and a proof an agent wrote is a cache hit for a later
autonomous run (the key is derived from the same material either way).
"""

from unittest.mock import patch

import pytest

from formal import session as sessions
from formal.checker import Outcome
from formal.session import PropertySpec, UnknownProperty


@pytest.fixture(autouse=True)
def isolated_sessions(monkeypatch):
    monkeypatch.setattr(sessions, "_SESSIONS", {})


def _spec(pid="p1", description="f is idempotent", formal=""):
    """The formal statement tracks the description: that is what tells two
    properties apart under the cache key, where the prose no longer does."""
    return PropertySpec(
        id=pid,
        description=description,
        kind="idempotence",
        function="f",
        function_code="def f(x): return x",
        formal=formal or f"forall x, {description}",
    )


def _verified(pid, lean="import Mathlib\ntheorem t : True := by trivial"):
    """A verdict Lean actually produced — `checked` is what the cache guard demands."""
    return Outcome(id=pid, status="verified", lean_code=lean, checked=True)


def _failed(pid, error="unknown identifier"):
    return Outcome(id=pid, status="failed", lean_code="bad", error=error, hint="try decide")


class TestCreate:
    def test_everything_is_work_when_the_cache_is_empty(self):
        session = sessions.create([_spec("p1"), _spec("p2", "f is total")])
        assert session.work_ids == ["p1", "p2"]
        assert session.cached_ids == []
        assert not session.complete

    def test_a_cache_hit_needs_no_proof(self):
        first = sessions.create([_spec()])
        with patch("formal.session.check_batch", return_value=[_verified("p1")]):
            sessions.check(first, {"p1": "import Mathlib\ntheorem t : True := by trivial"})

        second = sessions.create([_spec()])
        assert second.cached_ids == ["p1"]
        assert second.work_ids == []
        assert second.complete

    def test_distinct_properties_get_distinct_keys(self):
        session = sessions.create([_spec("p1", "f is idempotent"), _spec("p2", "f is total")])
        assert session.keys["p1"] != session.keys["p2"]

    def test_the_session_is_retrievable(self):
        session = sessions.create([_spec()])
        assert sessions.get(session.id) is session

    def test_an_unknown_session_is_none(self):
        assert sessions.get("nope") is None


class TestCheck:
    def test_a_verified_proof_settles_the_property(self):
        session = sessions.create([_spec()])
        with patch("formal.session.check_batch", return_value=[_verified("p1")]):
            outcomes = sessions.check(session, {"p1": "theorem t : True := by trivial"})

        assert [o.id for o in outcomes] == ["p1"]
        assert session.complete
        assert session.work_ids == []

    def test_a_failed_proof_stays_outstanding(self):
        session = sessions.create([_spec()])
        with patch("formal.session.check_batch", return_value=[_failed("p1")]):
            outcomes = sessions.check(session, {"p1": "nope"})

        assert not outcomes[0].verified
        assert session.work_ids == ["p1"]
        assert not session.complete

    def test_an_unregistered_id_is_rejected(self):
        session = sessions.create([_spec("p1")])
        with pytest.raises(UnknownProperty):
            sessions.check(session, {"p9": "theorem t : True := by trivial"})

    def test_a_settled_property_is_not_rechecked(self):
        """Resending the whole set after a partial failure must not re-import Mathlib."""
        session = sessions.create([_spec("p1"), _spec("p2", "f is total")])
        with patch("formal.session.check_batch", return_value=[_verified("p1"), _failed("p2")]):
            sessions.check(session, {"p1": "a", "p2": "b"})

        with patch("formal.session.check_batch", return_value=[_verified("p2")]) as check_batch:
            sessions.check(session, {"p1": "a", "p2": "b-fixed"})

        submitted = [s.id for s in check_batch.call_args[0][0]]
        assert submitted == ["p2"]

    def test_nothing_to_check_runs_no_lean(self):
        session = sessions.create([_spec()])
        with patch("formal.session.check_batch", return_value=[_verified("p1")]):
            sessions.check(session, {"p1": "a"})

        with patch("formal.session.check_batch") as check_batch:
            outcomes = sessions.check(session, {"p1": "a"})

        assert outcomes == []
        assert check_batch.call_count == 0

    def test_attempts_are_counted_per_property(self):
        session = sessions.create([_spec()])
        with patch("formal.session.check_batch", return_value=[_failed("p1")]):
            sessions.check(session, {"p1": "one"})
            sessions.check(session, {"p1": "two"})

        assert session.attempts["p1"] == 2


class TestCacheRoundTrip:
    def test_an_agent_proof_is_reusable_by_the_llm_path(self):
        """Same key material, so the two paths share one cache rather than two."""
        from formal import proof_cache

        spec = _spec()
        session = sessions.create([spec])
        proof = "import Mathlib\ntheorem t : True := by trivial"
        with patch("formal.session.check_batch", return_value=[_verified("p1", proof)]):
            sessions.check(session, {"p1": proof})

        cached = proof_cache.load(spec.cache_key())
        assert cached is not None
        assert cached.verified
        assert cached.lean_code == proof
        assert cached.description == spec.description

    def test_a_failure_is_never_cached(self):
        from formal import proof_cache

        spec = _spec()
        session = sessions.create([spec])
        with patch("formal.session.check_batch", return_value=[_failed("p1")]):
            sessions.check(session, {"p1": "bad"})

        assert proof_cache.load(spec.cache_key()) is None

    def test_retries_are_recorded_on_the_cached_result(self):
        from formal import proof_cache

        spec = _spec()
        session = sessions.create([spec])
        with patch("formal.session.check_batch", return_value=[_failed("p1")]):
            sessions.check(session, {"p1": "bad"})
        with patch("formal.session.check_batch", return_value=[_verified("p1")]):
            sessions.check(session, {"p1": "good"})

        assert proof_cache.load(spec.cache_key()).retries == 1


class TestLifecycle:
    def test_drop_removes_the_session(self):
        session = sessions.create([_spec()])
        assert sessions.drop(session.id)
        assert sessions.get(session.id) is None

    def test_dropping_twice_reports_the_second_as_absent(self):
        session = sessions.create([_spec()])
        sessions.drop(session.id)
        assert not sessions.drop(session.id)

    def test_an_expired_session_is_evicted(self, monkeypatch):
        session = sessions.create([_spec()])
        monkeypatch.setenv("SESSION_TTL_MINUTES", "1")
        session.created_at -= 120
        assert sessions.get(session.id) is None

    def test_a_fresh_session_survives_eviction(self, monkeypatch):
        monkeypatch.setenv("SESSION_TTL_MINUTES", "1")
        session = sessions.create([_spec()])
        assert sessions.get(session.id) is not None


class TestCacheGuard:
    """The cache outlives the run and is shared with the LLM path, so a wrong entry
    is served as truth indefinitely. Only an evidenced verdict may be written."""

    def _stored(self, spec):
        from formal import proof_cache

        return proof_cache.load(spec.cache_key())

    def test_a_verdict_lean_never_produced_is_not_cached(self):
        """The incident: a mocked verifier put lean_code "ok" into the real cache."""
        spec = _spec()
        session = sessions.create([spec])
        stub = Outcome(id="p1", status="verified", lean_code="ok")
        with patch("formal.session.check_batch", return_value=[stub]):
            sessions.check(session, {"p1": "ok"})

        assert self._stored(spec) is None

    def test_the_session_still_reports_it_verified(self):
        """Refusing to persist is not the same as overruling the checker."""
        spec = _spec()
        session = sessions.create([spec])
        stub = Outcome(id="p1", status="verified", lean_code="ok")
        with patch("formal.session.check_batch", return_value=[stub]):
            outcomes = sessions.check(session, {"p1": "ok"})

        assert outcomes[0].verified
        assert session.complete

    def test_a_proof_that_is_not_lean_is_not_cached(self):
        spec = _spec()
        session = sessions.create([spec])
        stub = Outcome(id="p1", status="verified", lean_code="looks fine to me", checked=True)
        with patch("formal.session.check_batch", return_value=[stub]):
            sessions.check(session, {"p1": "looks fine to me"})

        assert self._stored(spec) is None

    def test_a_proof_containing_sorry_is_not_cached(self):
        spec = _spec()
        session = sessions.create([spec])
        incomplete = "import Mathlib\ntheorem t : True := by sorry"
        stub = Outcome(id="p1", status="verified", lean_code=incomplete, checked=True)
        with patch("formal.session.check_batch", return_value=[stub]):
            sessions.check(session, {"p1": "x"})

        assert self._stored(spec) is None

    def test_an_evidenced_proof_is_cached(self):
        spec = _spec()
        session = sessions.create([spec])
        with patch("formal.session.check_batch", return_value=[_verified("p1")]):
            sessions.check(session, {"p1": "x"})

        assert self._stored(spec) is not None


class TestCacheHitIsAuditable:
    """Prose left the key, so a hit must say what it actually established.

    Two callers can agree on a formal statement while modelling it differently.
    The key cannot tell them apart, so the modelling recorded when the proof was
    accepted travels back with the hit and the caller decides whether it matches.
    """

    def _prove(self, spec, description, assumptions):
        stored = PropertySpec(
            id=spec.id,
            description=description,
            kind=spec.kind,
            function=spec.function,
            function_code=spec.function_code,
            formal=spec.formal,
            assumptions=assumptions,
        )
        session = sessions.create([stored])
        with patch("formal.session.check_batch", return_value=[_verified(stored.id)]):
            sessions.check(session, {stored.id: "x"})

    def test_a_hit_reports_what_was_proved(self):
        spec = _spec()
        self._prove(spec, "applying f twice changes nothing", ["Strings modeled as List Char"])

        reopened = sessions.create([spec])
        hit = reopened.hits["p1"]
        assert hit.description == "applying f twice changes nothing"
        assert hit.assumptions == ["Strings modeled as List Char"]

    def test_a_paraphrase_still_hits(self):
        """The point of the rework: different words, same theorem, no re-proof."""
        self._prove(_spec(formal="∀ x, f (f x) = f x"), "idempotent", [])

        reopened = sessions.create([_spec(description="totally different words", formal="forall x, f(f x) = f x")])
        assert reopened.cached_ids == ["p1"]

    def test_differing_assumptions_hit_but_are_visible(self):
        """The accepted risk: the caller has to read the hit to catch this."""
        spec = _spec()
        self._prove(spec, "same statement", ["floats modeled as rationals"])

        reopened = sessions.create([spec])
        assert reopened.cached_ids == ["p1"]
        assert reopened.hits["p1"].assumptions == ["floats modeled as rationals"]


class TestRegistryUnderConcurrency:
    """Sync endpoints run in a threadpool, so the registry has more than one caller.

    Eviction used to build a list of expired ids and then `del` each one. Two
    threads selecting the same id meant the second raised KeyError out of a
    request that had done nothing wrong.
    """

    def test_evicting_an_id_another_caller_already_removed_is_safe(self, monkeypatch):
        """The race, made deterministic — threads alone will not reproduce it reliably."""
        monkeypatch.setenv("SESSION_TTL_MINUTES", "1")
        session = sessions.create([_spec()])
        session.created_at -= 10_000

        class RegistryEmptiedByAnotherCaller(dict):
            def items(self):
                snapshot = list(super().items())
                self.clear()
                return snapshot

        monkeypatch.setattr(sessions, "_SESSIONS", RegistryEmptiedByAnotherCaller({session.id: session}))
        sessions._evict_expired()

    def test_churn_from_many_threads_leaves_the_registry_consistent(self):
        import threading

        errors = []

        def churn(n):
            try:
                for i in range(15):
                    session = sessions.create([_spec(f"p{n}_{i}")])
                    sessions.get(session.id)
                    sessions.drop(session.id)
            except Exception as e:  # noqa: BLE001 - the point is that nothing escapes
                errors.append(e)

        threads = [threading.Thread(target=churn, args=(n,)) for n in range(8)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert errors == []
        assert sessions._SESSIONS == {}

    def test_dropping_a_session_twice_from_two_callers_is_survivable(self):
        session = sessions.create([_spec()])
        assert sessions.drop(session.id)
        assert not sessions.drop(session.id)
