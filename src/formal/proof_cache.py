"""Disk-backed cache for verified Lean theorem results.

Cache key is a SHA-256 hash of what is being proved:
  - pure function source code, trailing whitespace removed
  - the property kind
  - the formal statement, with operator spelling and spacing normalised

Prose — the description, preconditions and assumptions — is deliberately not in
the key. See cache_key for why.

Only successful (verified) results are cached — failures are always retried.
"""

import hashlib
import json
import os
import re
from typing import TYPE_CHECKING

from .logger import get_logger, log
from .paths import PROOF_CACHE_DIR

if TYPE_CHECKING:
    from .property_verifier import PropertyResult

_log = get_logger(__name__)

_CACHE_DIR = PROOF_CACHE_DIR
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


_OPERATORS = {
    "∀": "forall",
    "∃": "exists",
    "→": "->",
    "⟶": "->",
    "↔": "<->",
    "∧": "/\\",
    "∨": "\\/",
    "¬": "not",
    "≠": "<>",
    "≤": "<=",
    "≥": ">=",
    "∈": " in ",
}


def normalise_formal(formal: str) -> str:
    """Reduce a formal statement to the form two writers of it should agree on.

    Operator spelling and spacing are free choices — `∀ x, p x → q x` and
    `forall x, p x -> q x` are one statement — and an agent picks differently
    from run to run where a fixed prompt at temperature 0 did not.
    """
    for symbol, ascii_form in _OPERATORS.items():
        formal = formal.replace(symbol, ascii_form)
    return re.sub(r"\s+", "", formal)


def normalise_code(function_code: str) -> str:
    """Indentation is meaning in Python, so only trailing and surrounding space goes."""
    return "\n".join(line.rstrip() for line in function_code.strip().splitlines())


def cache_key(function_code: str, kind: str, formal: str) -> str:
    """Identify a property by what is being proved, not by how it was described.

    The description, preconditions and assumptions that used to be mixed in here
    are English prose. A fixed prompt reproduces them verbatim, so the key worked
    while formal wrote them itself; an agent paraphrases, and every paraphrase was
    a fresh key and a re-proof. Across the 148 properties in a real run, the
    function, its kind and the normalised formal statement separate all of them.

    The prompt hash is gone with them. What is cached is a proof Lean accepted,
    and Lean's verdict does not depend on which prompt produced the theorem — and
    a prompt change that alters the formalisation changes `formal`, which changes
    the key anyway.
    """
    payload = "\n".join([normalise_code(function_code), kind.strip().lower(), normalise_formal(formal)])
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
