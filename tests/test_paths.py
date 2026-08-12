"""Tests for paths — env overrides and the checkout/XDG fallback chain."""

from pathlib import Path

from formal import paths


class TestFromEnv:
    def test_unset_falls_back_to_default(self, monkeypatch):
        monkeypatch.delenv("FORMAL_TEST_DIR", raising=False)
        assert paths._from_env("FORMAL_TEST_DIR", Path("/default")) == Path("/default")

    def test_blank_falls_back_to_default(self, monkeypatch):
        monkeypatch.setenv("FORMAL_TEST_DIR", "   ")
        assert paths._from_env("FORMAL_TEST_DIR", Path("/default")) == Path("/default")

    def test_set_value_wins(self, monkeypatch):
        monkeypatch.setenv("FORMAL_TEST_DIR", "/custom/dir")
        assert paths._from_env("FORMAL_TEST_DIR", Path("/default")) == Path("/custom/dir")

    def test_tilde_is_expanded(self, monkeypatch):
        monkeypatch.setenv("FORMAL_TEST_DIR", "~/somewhere")
        assert paths._from_env("FORMAL_TEST_DIR", Path("/default")) == Path.home() / "somewhere"


class TestDefaultHome:
    def test_prefers_the_checkout_it_was_installed_from(self):
        assert (paths._default_home() / "lean_project" / "lakefile.toml").is_file()

    def test_falls_back_to_xdg_data_home(self, monkeypatch, tmp_path):
        monkeypatch.setattr(paths, "__file__", str(tmp_path / "src" / "formal" / "paths.py"))
        monkeypatch.setenv("XDG_DATA_HOME", "/xdg/data")
        assert paths._default_home() == Path("/xdg/data/formal")

    def test_falls_back_to_local_share_without_xdg(self, monkeypatch, tmp_path):
        monkeypatch.setattr(paths, "__file__", str(tmp_path / "src" / "formal" / "paths.py"))
        monkeypatch.delenv("XDG_DATA_HOME", raising=False)
        assert paths._default_home() == Path.home() / ".local" / "share" / "formal"
