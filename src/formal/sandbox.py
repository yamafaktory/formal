"""Confinement for the Lean subprocess, which elaborates LLM-authored code.

Lean can execute arbitrary code while elaborating (`#eval`, macros, `initialize`),
so proofs are checked inside bubblewrap: no network, no home directory, and
nothing writable except the Lean project itself.
"""

import os
import shutil
from pathlib import Path

from .logger import get_logger, log
from .paths import LEAN_PROJECT_DIR
from .toolchain import elan_home

_log = get_logger(__name__)
_warned = False

_OFF = {"off", "none", "0", "false"}


def mode() -> str:
    return os.getenv("FORMAL_SANDBOX", "auto").strip().lower()


def available() -> str | None:
    return shutil.which("bwrap")


def describe() -> str:
    current = mode()
    if current in _OFF:
        return "off (FORMAL_SANDBOX)"
    if available() is None:
        return "unavailable — install bubblewrap"
    return "bubblewrap"


def wrap(cmd: list[str]) -> list[str]:
    """Return cmd wrapped in bubblewrap, or unchanged when sandboxing is unavailable."""
    global _warned

    current = mode()
    if current in _OFF:
        return cmd

    bwrap = available()
    if bwrap is None:
        if current == "bwrap":
            raise RuntimeError("FORMAL_SANDBOX=bwrap but bubblewrap is not installed")
        if not _warned:
            _warned = True
            log(
                _log,
                "LEAN",
                "bubblewrap not found — running Lean unsandboxed. "
                "Install bubblewrap, or set FORMAL_SANDBOX=off to silence this.",
            )
        return cmd

    home = Path.home()
    elan = elan_home()

    args = [
        bwrap,
        "--ro-bind",
        "/",
        "/",
        "--dev",
        "/dev",
        "--proc",
        "/proc",
        "--tmpfs",
        "/tmp",
        "--tmpfs",
        str(home),
        "--ro-bind-try",
        str(elan),
        str(elan),
        "--bind",
        str(LEAN_PROJECT_DIR),
        str(LEAN_PROJECT_DIR),
        "--chdir",
        str(LEAN_PROJECT_DIR),
        "--unshare-net",
        "--unshare-pid",
        "--unshare-ipc",
        "--unshare-uts",
        "--new-session",
        "--die-with-parent",
        "--",
    ]
    return args + cmd
