"""Disk-backed cache for verified Lean theorem results.

Cache key is a SHA-256 hash of the inputs that determine a proof:
  - pure function source code
  - property description, kind, and formal spec

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


def cache_key(function_code: str, description: str, kind: str, formal: str) -> str:
    payload = "\n".join([function_code, description, kind, formal])
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
