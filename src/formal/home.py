"""Where formal keeps its state, resolved without importing anything env-derived.

Kept separate from paths so the CLI can locate .env before path constants are
frozen at import time.
"""

import os
from pathlib import Path


def checkout_root() -> Path | None:
    candidate = Path(__file__).resolve().parents[2]
    return candidate if (candidate / "lean_project" / "lakefile.toml").is_file() else None


def default_home() -> Path:
    checkout = checkout_root()
    if checkout is not None:
        return checkout
    xdg = os.getenv("XDG_DATA_HOME", "").strip()
    return Path(xdg or Path.home() / ".local" / "share") / "formal"


def home() -> Path:
    value = os.getenv("FORMAL_HOME", "").strip()
    return Path(value).expanduser() if value else default_home()
