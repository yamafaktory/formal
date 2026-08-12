"""Locating the Lean toolchain without requiring it on the user's shell PATH."""

import os
import shutil
from pathlib import Path


def elan_home() -> Path:
    value = os.getenv("ELAN_HOME", "").strip()
    return Path(value).expanduser() if value else Path.home() / ".elan"


def bin_dir() -> Path:
    return elan_home() / "bin"


def search_path(base: str | None = None) -> str:
    current = os.environ.get("PATH", "") if base is None else base
    elan = str(bin_dir())
    if not bin_dir().is_dir() or elan in current.split(os.pathsep):
        return current
    return os.pathsep.join([elan, current]) if current else elan


def which(name: str) -> str | None:
    return shutil.which(name, path=search_path())


def env(base: dict | None = None) -> dict:
    merged = dict(os.environ if base is None else base)
    merged["PATH"] = search_path(merged.get("PATH"))
    return merged
