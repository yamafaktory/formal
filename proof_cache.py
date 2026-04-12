"""Disk-backed cache for verified Lean theorem results.

Cache key is a SHA-256 hash of the inputs that determine a proof:
  - pure function source code
  - property description, kind, and formal spec
  - preconditions and assumptions (affect the generated Lean theorem shape)

Only successful (verified) results are cached — failures are always retried.
"""

import hashlib
import json
import os
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .property_verifier import PropertyResult

_CACHE_DIR = Path(os.getenv("PROOF_CACHE_DIR", "/app/results/cache"))
_CACHE_TTL_DAYS = int(os.getenv("PROOF_CACHE_TTL_DAYS", "7"))


def _evict_expired() -> None:
    """Delete cache entries older than PROOF_CACHE_TTL_DAYS."""
    import time

    if not _CACHE_DIR.exists():
        return
    cutoff = time.time() - _CACHE_TTL_DAYS * 86400
    for path in _CACHE_DIR.glob("*.json"):
        if path.stat().st_mtime < cutoff:
            path.unlink(missing_ok=True)


def cache_key(
    function_code: str,
    description: str,
    kind: str,
    formal: str,
    preconditions: list[str],
    assumptions: list[str],
) -> str:
    payload = "\n".join([function_code, description, kind, formal, *preconditions, *assumptions])
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
    _CACHE_DIR.mkdir(parents=True, exist_ok=True)
    path = _CACHE_DIR / f"{key}.json"
    path.write_text(json.dumps(result.__dict__, indent=2))
    _evict_expired()
