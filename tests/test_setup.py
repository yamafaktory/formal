"""Tests for setup — .env round-tripping, prompts, and the Lean bootstrap."""

from unittest.mock import patch

import pytest

from formal import setup


@pytest.fixture
def env_path(tmp_path, monkeypatch):
    path = tmp_path / ".env"
    monkeypatch.setattr(setup, "env_file", lambda: path)
    return path


class TestReadEnv:
    def test_missing_file_is_empty(self, env_path):
        assert setup.read_env() == {}

    def test_parses_pairs_and_skips_noise(self, env_path):
        env_path.write_text("# comment\n\nA=1\nB = two \nbroken\n")
        assert setup.read_env() == {"A": "1", "B": "two"}


class TestWriteEnv:
    def test_creates_and_restricts_permissions(self, env_path):
        setup.write_env({"A": "1"})
        assert env_path.read_text() == "A=1\n"
        assert env_path.stat().st_mode & 0o777 == 0o600

    def test_preserves_unrelated_keys(self, env_path):
        env_path.write_text("KEEP=yes\nA=old\n")
        setup.write_env({"A": "new"})
        assert setup.read_env() == {"KEEP": "yes", "A": "new"}

    def test_drops_requested_keys(self, env_path):
        env_path.write_text("STALE=1\nKEEP=1\n")
        setup.write_env({}, drop=("STALE",))
        assert setup.read_env() == {"KEEP": "1"}

    def test_dropping_an_absent_key_is_harmless(self, env_path):
        setup.write_env({"A": "1"}, drop=("NOPE",))
        assert setup.read_env() == {"A": "1"}


class TestPrompts:
    def test_ask_returns_default_on_blank(self, monkeypatch):
        monkeypatch.setattr("builtins.input", lambda _: "  ")
        assert setup._ask("? ", "fallback") == "fallback"

    def test_ask_returns_default_on_eof(self, monkeypatch):
        def raise_eof(_):
            raise EOFError

        monkeypatch.setattr("builtins.input", raise_eof)
        assert setup._ask("? ", "fallback") == "fallback"

    @pytest.mark.parametrize(
        ("answer", "expected"),
        [("", True), ("y", True), ("Y", True), ("n", False), ("no", False)],
    )
    def test_confirm_defaults_to_yes(self, monkeypatch, answer, expected):
        monkeypatch.setattr("builtins.input", lambda _: answer)
        assert setup._confirm("? ") is expected

    def test_pick_rejects_out_of_range_then_accepts(self, monkeypatch):
        answers = iter(["9", "0", "abc", "2"])
        monkeypatch.setattr("builtins.input", lambda _: next(answers))
        assert setup._pick(["a", "b"], "? ") == "b"


class TestChooseModel:
    def test_falls_back_to_manual_entry(self, monkeypatch):
        monkeypatch.setattr("builtins.input", lambda _: "typed-model")
        assert setup._choose_model([]) == "typed-model"

    def test_refuses_an_empty_manual_entry(self, monkeypatch):
        monkeypatch.setattr("builtins.input", lambda _: "")
        with pytest.raises(SystemExit):
            setup._choose_model([])


class TestInstallLean:
    def test_skips_when_mathlib_is_already_built(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup.toolchain, "which", lambda _: "/usr/bin/lake")
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path)
        with patch.object(setup, "_lake") as lake:
            assert setup.install_lean() is True
        lake.assert_not_called()

    def test_declining_the_download_stops(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup.toolchain, "which", lambda _: "/usr/bin/lake")
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path / "absent")
        monkeypatch.setattr("builtins.input", lambda _: "n")
        with patch.object(setup, "_lake") as lake:
            assert setup.install_lean() is False
        lake.assert_not_called()

    def test_runs_the_three_lake_steps_in_order(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup.toolchain, "which", lambda _: "/usr/bin/lake")
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path / "absent")
        monkeypatch.setattr("builtins.input", lambda _: "y")
        with patch.object(setup, "_lake", return_value=True) as lake:
            assert setup.install_lean() is True
        assert [call.args for call in lake.call_args_list] == [
            ("update",),
            ("exe", "cache", "get"),
            ("build", "Warmup"),
        ]

    def test_a_failing_step_aborts_the_rest(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup.toolchain, "which", lambda _: "/usr/bin/lake")
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path / "absent")
        monkeypatch.setattr("builtins.input", lambda _: "y")
        with patch.object(setup, "_lake", return_value=False) as lake:
            assert setup.install_lean() is False
        assert lake.call_count == 1

    def test_declining_elan_stops_before_lake(self, monkeypatch):
        monkeypatch.setattr(setup.toolchain, "which", lambda _: None)
        monkeypatch.setattr("builtins.input", lambda _: "n")
        with patch.object(setup, "_lake") as lake:
            assert setup.install_lean() is False
        lake.assert_not_called()


class TestRun:
    def test_lean_only_skips_backend_configuration(self, monkeypatch):
        monkeypatch.setattr(setup, "install_lean", lambda: True)
        monkeypatch.setattr(setup.sandbox, "available", lambda: "/usr/bin/bwrap")
        with patch.object(setup, "configure_backend") as configure:
            assert setup.run(lean_only=True) == 0
        configure.assert_not_called()

    def test_backend_only_skips_the_lean_install(self, monkeypatch):
        monkeypatch.setattr(setup.sandbox, "available", lambda: "/usr/bin/bwrap")
        with patch.object(setup, "install_lean") as install, patch.object(setup, "configure_backend"):
            assert setup.run(backend_only=True) == 0
        install.assert_not_called()

    def test_a_failed_lean_install_is_reported(self, monkeypatch):
        monkeypatch.setattr(setup, "install_lean", lambda: False)
        with patch.object(setup, "configure_backend") as configure:
            assert setup.run() == 1
        configure.assert_not_called()
