"""Tests for sandbox — mode handling, wrapping, and real confinement under bwrap."""

import subprocess
from pathlib import Path

import pytest

from formal import sandbox

_CMD = ["lean", "--json", "/lean_project/Verify/tmp_x.lean"]


class TestMode:
    @pytest.mark.parametrize("value", ["off", "none", "0", "false", "OFF", " off "])
    def test_disabled_returns_command_unchanged(self, monkeypatch, value):
        monkeypatch.setenv("FORMAL_SANDBOX", value)
        assert sandbox.wrap(_CMD) == _CMD

    def test_defaults_to_auto(self, monkeypatch):
        monkeypatch.delenv("FORMAL_SANDBOX", raising=False)
        assert sandbox.mode() == "auto"

    def test_auto_without_bwrap_runs_unwrapped(self, monkeypatch):
        monkeypatch.setenv("FORMAL_SANDBOX", "auto")
        monkeypatch.setattr(sandbox, "available", lambda: None)
        monkeypatch.setattr(sandbox, "_warned", False)
        assert sandbox.wrap(_CMD) == _CMD

    def test_explicit_bwrap_without_bwrap_raises(self, monkeypatch):
        monkeypatch.setenv("FORMAL_SANDBOX", "bwrap")
        monkeypatch.setattr(sandbox, "available", lambda: None)
        with pytest.raises(RuntimeError, match="not installed"):
            sandbox.wrap(_CMD)


class TestWrapping:
    @pytest.fixture
    def wrapped(self, monkeypatch):
        monkeypatch.setenv("FORMAL_SANDBOX", "auto")
        monkeypatch.setattr(sandbox, "available", lambda: "/usr/bin/bwrap")
        return sandbox.wrap(_CMD)

    def test_command_is_preserved_after_the_separator(self, wrapped):
        assert wrapped[wrapped.index("--") + 1 :] == _CMD

    def test_network_and_namespaces_are_unshared(self, wrapped):
        for flag in ("--unshare-net", "--unshare-pid", "--unshare-ipc", "--unshare-uts"):
            assert flag in wrapped

    def test_dies_with_parent_and_detaches_the_terminal(self, wrapped):
        assert "--die-with-parent" in wrapped
        assert "--new-session" in wrapped

    def test_home_is_masked_by_a_tmpfs(self, wrapped):
        pairs = list(zip(wrapped, wrapped[1:]))
        assert ("--tmpfs", str(Path.home())) in pairs

    def test_root_is_bound_read_only(self, wrapped):
        triples = list(zip(wrapped, wrapped[1:], wrapped[2:]))
        assert ("--ro-bind", "/", "/") in triples

    def test_lean_project_stays_writable(self, wrapped):
        from formal.paths import LEAN_PROJECT_DIR

        triples = list(zip(wrapped, wrapped[1:], wrapped[2:]))
        assert ("--bind", str(LEAN_PROJECT_DIR), str(LEAN_PROJECT_DIR)) in triples

    def test_home_is_masked_before_lean_project_is_restored(self, wrapped):
        from formal.paths import LEAN_PROJECT_DIR

        if not str(LEAN_PROJECT_DIR).startswith(str(Path.home())):
            pytest.skip("lean project lives outside the home directory")
        assert wrapped.index(str(Path.home())) < wrapped.index(str(LEAN_PROJECT_DIR))


@pytest.mark.skipif(sandbox.available() is None, reason="bubblewrap is not installed")
class TestRealConfinement:
    def _run(self, monkeypatch, argv):
        monkeypatch.setenv("FORMAL_SANDBOX", "auto")
        return subprocess.run(sandbox.wrap(argv), capture_output=True, text=True, timeout=30)

    def test_home_is_not_readable(self, monkeypatch, tmp_path):
        secret = Path.home() / ".claude"
        if not secret.exists():
            pytest.skip("no ~/.claude on this machine")
        result = self._run(monkeypatch, ["cat", str(secret / "settings.json")])
        assert result.returncode != 0

    def test_network_is_unreachable(self, monkeypatch):
        result = self._run(
            monkeypatch,
            ["python3", "-c", "import socket; socket.create_connection(('1.1.1.1', 443), 5)"],
        )
        assert result.returncode != 0

    def test_lean_project_is_readable(self, monkeypatch):
        from formal.paths import LEAN_PROJECT_DIR

        result = self._run(monkeypatch, ["cat", str(LEAN_PROJECT_DIR / "lean-toolchain")])
        assert result.returncode == 0
        assert "leanprover" in result.stdout
