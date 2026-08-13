"""Sessions for caller-supplied proofs.

A session holds the property metadata once, so a retry carries only Lean. The
caller registers what it intends to prove, learns which properties the cache has
already settled, and then submits proofs by id until nothing is left failing.

Registering is also what makes the cache work in both directions: the key is
derived from the same material the LLM pipeline uses, so a proof written by an
agent is a cache hit for a later autonomous run, and the reverse.
"""

import os
import time
import uuid
from dataclasses import dataclass, field

from . import proof_cache
from .checker import Outcome, Submission, can_cache, check_batch
from .logger import get_logger, log
from .property_verifier import PropertyResult

_log = get_logger(__name__)

_SESSIONS: dict[str, "Session"] = {}


def _ttl_seconds() -> int:
    return max(60, int(os.getenv("SESSION_TTL_MINUTES", "60")) * 60)


@dataclass
class PropertySpec:
    """What the caller intends to prove about one function."""

    id: str
    description: str
    kind: str = ""
    function: str = ""
    function_code: str = ""
    formal: str = ""
    preconditions: list[str] = field(default_factory=list)
    assumptions: list[str] = field(default_factory=list)

    def cache_key(self) -> str:
        return proof_cache.cache_key(
            self.function_code,
            self.description,
            self.kind,
            self.formal,
            self.preconditions,
            self.assumptions,
        )


@dataclass
class Session:
    id: str
    created_at: float
    specs: dict[str, PropertySpec]
    keys: dict[str, str]
    verified: dict[str, str] = field(default_factory=dict)
    attempts: dict[str, int] = field(default_factory=dict)

    @property
    def cached_ids(self) -> list[str]:
        return [pid for pid in self.specs if pid in self.verified]

    @property
    def work_ids(self) -> list[str]:
        return [pid for pid in self.specs if pid not in self.verified]

    @property
    def complete(self) -> bool:
        return not self.work_ids


def _evict_expired() -> None:
    cutoff = time.time() - _ttl_seconds()
    for sid in [s for s, sess in _SESSIONS.items() if sess.created_at < cutoff]:
        del _SESSIONS[sid]


def create(specs: list[PropertySpec]) -> Session:
    """Open a session, settling whatever the proof cache already knows."""
    _evict_expired()

    session = Session(
        id=uuid.uuid4().hex,
        created_at=time.time(),
        specs={spec.id: spec for spec in specs},
        keys={spec.id: spec.cache_key() for spec in specs},
    )
    for spec in specs:
        cached = proof_cache.load(session.keys[spec.id])
        if cached is not None and cached.verified:
            session.verified[spec.id] = cached.lean_code
            log(_log, "CACHE", f"{spec.id} cache hit — no proof needed")

    _SESSIONS[session.id] = session
    log(
        _log,
        "SESSION",
        f"{session.id[:8]} opened — {len(session.cached_ids)} cached, {len(session.work_ids)} to prove",
    )
    return session


def get(session_id: str) -> Session | None:
    _evict_expired()
    return _SESSIONS.get(session_id)


def drop(session_id: str) -> bool:
    return _SESSIONS.pop(session_id, None) is not None


class UnknownProperty(KeyError):
    """A proof was submitted for an id the session never registered."""


def check(session: Session, proofs: dict[str, str]) -> list[Outcome]:
    """Check submitted proofs, caching what Lean accepts.

    Ids already verified are skipped rather than re-checked — resubmitting the
    whole set after a partial failure is the natural thing for a caller to do,
    and it should not cost another Mathlib import per settled property.
    """
    unknown = sorted(set(proofs) - set(session.specs))
    if unknown:
        raise UnknownProperty(f"not registered in this session: {', '.join(unknown)}")

    submissions = [Submission(id=pid, lean_code=lean) for pid, lean in proofs.items() if pid not in session.verified]
    for sub in submissions:
        session.attempts[sub.id] = session.attempts.get(sub.id, 0) + 1

    if not submissions:
        return []

    outcomes = check_batch(submissions)
    for outcome in outcomes:
        if not outcome.verified:
            continue
        session.verified[outcome.id] = outcome.lean_code
        if can_cache(outcome):
            _cache(session, outcome)
        else:
            log(_log, "CACHE", f"{outcome.id} verified but not cached — no evidence Lean accepted this proof")
    return outcomes


def _cache(session: Session, outcome: Outcome) -> None:
    spec = session.specs[outcome.id]
    proof_cache.save(
        session.keys[outcome.id],
        PropertyResult(
            property_id=spec.id,
            description=spec.description,
            kind=spec.kind,
            function=spec.function,
            verified=True,
            lean_code=outcome.lean_code,
            lean_output="",
            retries=max(0, session.attempts.get(outcome.id, 1) - 1),
            status="verified",
            preconditions=spec.preconditions,
            assumptions=spec.assumptions,
        ),
    )
