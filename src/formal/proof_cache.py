"""Disk-backed cache for verified Lean theorem results.

Cache key is a SHA-256 hash of the inputs that determine a proof:
  - pure function source code
  - property description, kind, and formal spec
  - preconditions and assumptions (affect the generated Lean theorem shape)
  - a short hash of the proof-generation prompts (invalidates on prompt changes)

Only successful (verified) results are cached — failures are always retried.
"""

import hashlib
import json
import os
from typing import TYPE_CHECKING

from .logger import get_logger, log
from .paths import PROOF_CACHE_DIR

if TYPE_CHECKING:
    from .property_verifier import PropertyResult

_log = get_logger(__name__)

_CACHE_DIR = PROOF_CACHE_DIR
_CACHE_TTL_DAYS = int(os.getenv("PROOF_CACHE_TTL_DAYS", "7"))


def _prompt_hash() -> str:
    """Short hash of proof-generation prompts — changes when prompts are edited."""
    from . import prompts

    content = "\n".join(
        [
            prompts.AUTOFORMALIZE_SYSTEM,
            prompts.PROPERTY_FORMALIZE_AND_PROVE_USER,
            prompts.PROOF_GENERATION_SYSTEM,
            prompts.PROOF_RETRY_USER,
        ]
    )
    return hashlib.sha256(content.encode()).hexdigest()[:8]


_PROMPT_HASH = _prompt_hash()


def _evict_expired() -> None:
    """Delete cache entries older than PROOF_CACHE_TTL_DAYS."""
    import time

    if not _CACHE_DIR.exists():
        return
    cutoff = time.time() - _CACHE_TTL_DAYS * 86400
    for path in _CACHE_DIR.glob("*.json"):
        if path.stat().st_mtime < cutoff:
            path.unlink(missing_ok=True)


def json_key(*parts: str) -> str:
    return hashlib.sha256("\n".join(parts).encode()).hexdigest()


def load_json(name: str) -> dict | None:
    path = _CACHE_DIR / f"{name}.json"
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text())
    except Exception:
        return None


def save_json(name: str, payload: dict) -> None:
    """Best-effort — a cache miss must never be worse than a write failure."""
    try:
        _CACHE_DIR.mkdir(parents=True, exist_ok=True)
        (_CACHE_DIR / f"{name}.json").write_text(json.dumps(payload, indent=2))
    except OSError as e:
        log(_log, "CACHE", f"could not write {name[:20]}… — {e}")


def cache_key(
    function_code: str,
    description: str,
    kind: str,
    formal: str,
    preconditions: list[str],
    assumptions: list[str],
) -> str:
    payload = "\n".join([_PROMPT_HASH, function_code, description, kind, formal, *preconditions, *assumptions])
    return hashlib.sha256(payload.encode()).hexdigest()


def load(key: str) -> "PropertyResult | None":
    from .property_verifier import PropertyResult

    path = _CACHE_DIR / f"{key}.json"
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text())
        return PropertyResult(**data)
    except Exception:
        return None


def save(key: str, result: "PropertyResult") -> None:
    """Best-effort — the cache is an optimisation and never changes a verdict."""
    try:
        _CACHE_DIR.mkdir(parents=True, exist_ok=True)
        path = _CACHE_DIR / f"{key}.json"
        path.write_text(json.dumps(result.__dict__, indent=2))
        _evict_expired()
    except OSError as e:
        log(_log, "CACHE", f"could not write {key[:12]}… — {e}")
