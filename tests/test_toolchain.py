"""Tests for toolchain — elan discovery and PATH augmentation."""

import os
from pathlib import Path

from formal import toolchain


class TestElanHome:
    def test_defaults_to_dot_elan(self, monkeypatch):
        monkeypatch.delenv("ELAN_HOME", raising=False)
        assert toolchain.elan_home() == Path.home() / ".elan"
        assert toolchain.bin_dir() == Path.home() / ".elan" / "bin"

    def test_env_override_is_expanded(self, monkeypatch):
        monkeypatch.setenv("ELAN_HOME", "~/elsewhere/elan")
        assert toolchain.elan_home() == Path.home() / "elsewhere" / "elan"

    def test_blank_env_falls_back(self, monkeypatch):
        monkeypatch.setenv("ELAN_HOME", "  ")
        assert toolchain.elan_home() == Path.home() / ".elan"


class TestSearchPath:
    def _with_elan(self, monkeypatch, tmp_path):
        (tmp_path / "bin").mkdir()
        monkeypatch.setenv("ELAN_HOME", str(tmp_path))
        return str(tmp_path / "bin")

    def test_prepends_elan_bin(self, monkeypatch, tmp_path):
        elan_bin = self._with_elan(monkeypatch, tmp_path)
        assert toolchain.search_path("/usr/bin") == f"{elan_bin}{os.pathsep}/usr/bin"

    def test_does_not_duplicate_an_entry_already_present(self, monkeypatch, tmp_path):
        elan_bin = self._with_elan(monkeypatch, tmp_path)
        base = f"/usr/bin{os.pathsep}{elan_bin}"
        assert toolchain.search_path(base) == base

    def test_missing_elan_dir_leaves_path_untouched(self, monkeypatch, tmp_path):
        monkeypatch.setenv("ELAN_HOME", str(tmp_path / "absent"))
        assert toolchain.search_path("/usr/bin") == "/usr/bin"

    def test_empty_base_yields_just_elan(self, monkeypatch, tmp_path):
        elan_bin = self._with_elan(monkeypatch, tmp_path)
        assert toolchain.search_path("") == elan_bin


class TestEnv:
    def test_augments_path_without_dropping_other_variables(self, monkeypatch, tmp_path):
        elan_bin = self._elan(monkeypatch, tmp_path)
        result = toolchain.env({"PATH": "/usr/bin", "LEAN_PATH": "/x"})
        assert result["PATH"] == f"{elan_bin}{os.pathsep}/usr/bin"
        assert result["LEAN_PATH"] == "/x"

    def test_defaults_to_the_process_environment(self, monkeypatch, tmp_path):
        elan_bin = self._elan(monkeypatch, tmp_path)
        monkeypatch.setenv("PATH", "/usr/bin")
        assert toolchain.env()["PATH"] == f"{elan_bin}{os.pathsep}/usr/bin"

    def _elan(self, monkeypatch, tmp_path):
        (tmp_path / "bin").mkdir()
        monkeypatch.setenv("ELAN_HOME", str(tmp_path))
        return str(tmp_path / "bin")


class TestWhich:
    def test_finds_a_binary_under_elan(self, monkeypatch, tmp_path):
        bin_dir = tmp_path / "bin"
        bin_dir.mkdir()
        fake = bin_dir / "lake"
        fake.write_text("#!/bin/sh\n")
        fake.chmod(0o755)
        monkeypatch.setenv("ELAN_HOME", str(tmp_path))
        monkeypatch.setenv("PATH", "/nonexistent")
        assert toolchain.which("lake") == str(fake)

    def test_returns_none_when_absent(self, monkeypatch, tmp_path):
        monkeypatch.setenv("ELAN_HOME", str(tmp_path / "absent"))
        monkeypatch.setenv("PATH", "/nonexistent")
        assert toolchain.which("lake") is None
