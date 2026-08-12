"""Filesystem locations, resolved from the checkout the package was installed from."""

import os
from pathlib import Path


def _default_home() -> Path:
    candidate = Path(__file__).resolve().parents[2]
    if (candidate / "lean_project" / "lakefile.toml").is_file():
        return candidate
    xdg = os.getenv("XDG_DATA_HOME", "").strip()
    return Path(xdg or Path.home() / ".local" / "share") / "formal"


def _from_env(name: str, default: Path) -> Path:
    value = os.getenv(name, "").strip()
    return Path(value).expanduser() if value else default


FORMAL_HOME = _from_env("FORMAL_HOME", _default_home())
LEAN_PROJECT_DIR = _from_env("LEAN_PROJECT_DIR", FORMAL_HOME / "lean_project")
RESULTS_DIR = _from_env("FORMAL_RESULTS_DIR", FORMAL_HOME / "results")
PROOF_CACHE_DIR = _from_env("PROOF_CACHE_DIR", RESULTS_DIR / "cache")
