"""Reaching the HTTP server, and starting it when nothing is listening.

An agent invoking formal from an arbitrary directory cannot assume a server is up,
and cannot run one in the foreground — a command that never returns is a command it
cannot use. Both are the same problem: starting the server has to be safe to do
unconditionally, and it has to come back.
"""

import os
import signal
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

from .paths import FORMAL_HOME

DEFAULT_HOST = "127.0.0.1"
DEFAULT_PORT = 1337


def host() -> str:
    return os.getenv("FORMAL_HOST", "").strip() or DEFAULT_HOST


def port() -> int:
    raw = os.getenv("FORMAL_PORT", "").strip()
    if not raw:
        return DEFAULT_PORT
    try:
        return int(raw)
    except ValueError:
        return DEFAULT_PORT


def base_url(server_host: str | None = None, server_port: int | None = None) -> str:
    return f"http://{server_host or host()}:{server_port or port()}"


def pid_file() -> Path:
    return FORMAL_HOME / "server.pid"


def log_file() -> Path:
    return FORMAL_HOME / "server.log"


def is_running(server_host: str | None = None, server_port: int | None = None, timeout: float = 0.5) -> bool:
    """True when something answers /health — the only claim worth making about it."""
    try:
        with urllib.request.urlopen(f"{base_url(server_host, server_port)}/health", timeout=timeout) as response:
            return response.status == 200
    except (urllib.error.URLError, OSError, ValueError):
        return False


def start(server_host: str | None = None, server_port: int | None = None, wait: float = 30.0) -> str:
    """Start the server unless it is already up, and return once it answers.

    Idempotent on purpose: a caller that cannot see the machine's process list
    should be able to run this before every request without thinking about it.
    """
    server_host, server_port = server_host or host(), server_port or port()
    url = base_url(server_host, server_port)
    if is_running(server_host, server_port):
        return url

    FORMAL_HOME.mkdir(parents=True, exist_ok=True)
    with log_file().open("ab") as handle:
        process = subprocess.Popen(
            [sys.executable, "-m", "formal.cli", "serve", "--host", server_host, "--port", str(server_port)],
            stdout=handle,
            stderr=handle,
            stdin=subprocess.DEVNULL,
            start_new_session=True,
        )
    pid_file().write_text(str(process.pid))

    deadline = time.monotonic() + wait
    while time.monotonic() < deadline:
        if is_running(server_host, server_port):
            return url
        if process.poll() is not None:
            raise RuntimeError(f"server exited immediately (code {process.returncode}) — see {log_file()}")
        time.sleep(0.2)
    raise RuntimeError(f"server did not answer on {url} within {wait:.0f}s — see {log_file()}")


def _recorded_pid() -> int | None:
    try:
        return int(pid_file().read_text().strip())
    except (OSError, ValueError):
        return None


def _is_ours(pid: int) -> bool:
    """Guard against a stale pid file naming a process the OS has since reused."""
    try:
        cmdline = Path(f"/proc/{pid}/cmdline").read_bytes()
    except OSError:
        return True
    return b"formal" in cmdline


def stop(server_host: str | None = None, server_port: int | None = None, wait: float = 10.0) -> bool:
    """Stop a server we started. False when there was nothing of ours to stop."""
    pid = _recorded_pid()
    if pid is None or not _is_ours(pid):
        pid_file().unlink(missing_ok=True)
        return False

    try:
        os.kill(pid, signal.SIGTERM)
    except ProcessLookupError:
        pid_file().unlink(missing_ok=True)
        return False
    except PermissionError:
        return False

    deadline = time.monotonic() + wait
    while time.monotonic() < deadline:
        if not is_running(server_host, server_port):
            pid_file().unlink(missing_ok=True)
            return True
        time.sleep(0.2)
    return False
