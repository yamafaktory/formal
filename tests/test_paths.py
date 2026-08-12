"""Tests for paths and home — env overrides and the checkout/XDG fallback chain."""

from pathlib import Path

from formal import home, paths


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


class TestCheckoutRoot:
    def test_detects_the_checkout_it_was_installed_from(self):
        root = home.checkout_root()
        assert root is not None
        assert (root / "lean_project" / "lakefile.toml").is_file()

    def test_none_when_installed_outside_a_checkout(self, monkeypatch, tmp_path):
        monkeypatch.setattr(home, "__file__", str(tmp_path / "site-packages" / "formal" / "home.py"))
        assert home.checkout_root() is None


class TestDefaultHome:
    def test_prefers_the_checkout(self):
        assert home.default_home() == home.checkout_root()

    def test_falls_back_to_xdg_data_home(self, monkeypatch, tmp_path):
        monkeypatch.setattr(home, "__file__", str(tmp_path / "site-packages" / "formal" / "home.py"))
        monkeypatch.setenv("XDG_DATA_HOME", "/xdg/data")
        assert home.default_home() == Path("/xdg/data/formal")

    def test_falls_back_to_local_share_without_xdg(self, monkeypatch, tmp_path):
        monkeypatch.setattr(home, "__file__", str(tmp_path / "site-packages" / "formal" / "home.py"))
        monkeypatch.delenv("XDG_DATA_HOME", raising=False)
        assert home.default_home() == Path.home() / ".local" / "share" / "formal"


class TestHome:
    def test_formal_home_overrides_everything(self, monkeypatch):
        monkeypatch.setenv("FORMAL_HOME", "~/elsewhere")
        assert home.home() == Path.home() / "elsewhere"

    def test_blank_formal_home_is_ignored(self, monkeypatch):
        monkeypatch.setenv("FORMAL_HOME", "  ")
        assert home.home() == home.default_home()
