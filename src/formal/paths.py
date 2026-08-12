"""Filesystem locations, resolved from the checkout or the XDG data directory."""

import os
from pathlib import Path

from .home import home


def _from_env(name: str, default: Path) -> Path:
    value = os.getenv(name, "").strip()
    return Path(value).expanduser() if value else default


FORMAL_HOME = home()
LEAN_PROJECT_DIR = _from_env("LEAN_PROJECT_DIR", FORMAL_HOME / "lean_project")
RESULTS_DIR = _from_env("FORMAL_RESULTS_DIR", FORMAL_HOME / "results")
PROOF_CACHE_DIR = _from_env("PROOF_CACHE_DIR", RESULTS_DIR / "cache")
