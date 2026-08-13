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


class TestEnsureElan:
    def test_existing_lake_needs_no_install(self, monkeypatch):
        monkeypatch.setattr(setup.toolchain, "which", lambda name: "/usr/bin/lake" if name == "lake" else None)
        with patch.object(setup, "install_elan") as install:
            assert setup.ensure_elan() is True
        install.assert_not_called()

    def test_elan_from_a_package_manager_needs_no_install(self, monkeypatch):
        monkeypatch.setattr(setup.toolchain, "which", lambda name: "/usr/bin/elan" if name == "elan" else None)
        with patch.object(setup, "install_elan") as install:
            assert setup.ensure_elan() is True
        install.assert_not_called()


class TestEnsureToolchain:
    def _elan_only(self, monkeypatch):
        monkeypatch.setattr(setup.toolchain, "which", lambda name: "/usr/bin/elan" if name == "elan" else None)

    def test_without_elan_falls_back_to_looking_for_lake(self, monkeypatch):
        monkeypatch.setattr(setup.toolchain, "which", lambda name: "/usr/bin/lake" if name == "lake" else None)
        with patch.object(setup.subprocess, "run") as run:
            assert setup.ensure_toolchain() is True
        run.assert_not_called()

    def test_an_installed_pin_is_left_alone(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path)
        (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.29.0\n")
        self._elan_only(monkeypatch)
        monkeypatch.setattr(setup, "toolchain_installed", lambda *a: True)
        with patch.object(setup.subprocess, "run") as run:
            assert setup.ensure_toolchain() is True
        run.assert_not_called()

    def test_a_lake_shim_alone_does_not_count_as_installed(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path)
        (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.29.0\n")
        monkeypatch.setattr(setup.toolchain, "which", lambda name: f"/usr/bin/{name}")
        monkeypatch.setattr(setup, "toolchain_installed", lambda *a: False)
        seen = []

        def run(cmd, **kwargs):
            seen.append(cmd)
            return type("R", (), {"returncode": 0})()

        monkeypatch.setattr(setup.subprocess, "run", run)
        assert setup.ensure_toolchain() is True
        assert seen == [["/usr/bin/elan", "toolchain", "install", "leanprover/lean4:v4.29.0"]]

    def test_reports_a_failed_toolchain_install(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path)
        (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.29.0\n")
        self._elan_only(monkeypatch)
        monkeypatch.setattr(setup, "toolchain_installed", lambda *a: False)
        monkeypatch.setattr(setup.subprocess, "run", lambda *a, **k: type("R", (), {"returncode": 1})())
        assert setup.ensure_toolchain() is False

    def test_missing_lean_toolchain_file_is_reported(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path)
        self._elan_only(monkeypatch)
        assert setup.ensure_toolchain() is False


class TestToolchainInstalled:
    def _list_output(self, monkeypatch, stdout, returncode=0):
        monkeypatch.setattr(
            setup.subprocess,
            "run",
            lambda *a, **k: type("R", (), {"returncode": returncode, "stdout": stdout})(),
        )

    def test_finds_the_pin_among_installed_toolchains(self, monkeypatch):
        self._list_output(monkeypatch, "leanprover/lean4:v4.29.0 (default)\nstable\n")
        assert setup.toolchain_installed("/usr/bin/elan", "leanprover/lean4:v4.29.0") is True

    def test_a_different_version_does_not_count(self, monkeypatch):
        self._list_output(monkeypatch, "leanprover/lean4:v4.28.0\n")
        assert setup.toolchain_installed("/usr/bin/elan", "leanprover/lean4:v4.29.0") is False

    def test_no_installed_toolchains(self, monkeypatch):
        self._list_output(monkeypatch, "")
        assert setup.toolchain_installed("/usr/bin/elan", "leanprover/lean4:v4.29.0") is False

    def test_a_failing_elan_reports_not_installed(self, monkeypatch):
        self._list_output(monkeypatch, "leanprover/lean4:v4.29.0\n", returncode=1)
        assert setup.toolchain_installed("/usr/bin/elan", "leanprover/lean4:v4.29.0") is False


class TestLeanVersion:
    def test_reads_and_strips_the_pin(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path)
        (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.29.0\n")
        assert setup.lean_version() == "leanprover/lean4:v4.29.0"

    def test_none_when_absent(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path)
        assert setup.lean_version() is None


class TestMaterializeLeanProject:
    """Outside a checkout the Lean project is created from files bundled in the wheel."""

    def _template(self, monkeypatch, tmp_path):
        source = tmp_path / "bundled"
        source.mkdir()
        for name in setup.TEMPLATE_FILES:
            (source / name).write_text(f"contents of {name}\n")
        monkeypatch.setattr(setup, "template_dir", lambda: source)
        return source

    def test_copies_the_bundled_project(self, monkeypatch, tmp_path):
        self._template(monkeypatch, tmp_path)
        target = tmp_path / "home" / "lean_project"
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", target)

        assert setup.materialize_lean_project() is True
        for name in setup.TEMPLATE_FILES:
            assert (target / name).is_file()
        assert (target / "Verify").is_dir()

    def test_an_existing_project_is_never_overwritten(self, monkeypatch, tmp_path):
        self._template(monkeypatch, tmp_path)
        target = tmp_path / "checkout" / "lean_project"
        target.mkdir(parents=True)
        (target / "lakefile.toml").write_text("mine\n")
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", target)

        assert setup.materialize_lean_project() is True
        assert (target / "lakefile.toml").read_text() == "mine\n"

    def test_reports_when_no_bundled_copy_exists(self, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "template_dir", lambda: tmp_path / "absent")
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path / "home" / "lean_project")
        assert setup.materialize_lean_project() is False

    def test_the_checkout_ships_every_template_file(self):
        from formal.home import checkout_root

        for name in setup.TEMPLATE_FILES:
            assert (checkout_root() / "lean_project" / name).is_file()


class TestInstallLean:
    @pytest.fixture
    def toolchain_ready(self, monkeypatch):
        monkeypatch.setattr(setup, "materialize_lean_project", lambda: True)
        monkeypatch.setattr(setup, "ensure_elan", lambda: True)
        monkeypatch.setattr(setup, "ensure_toolchain", lambda: True)

    def test_skips_when_mathlib_is_already_built(self, toolchain_ready, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path)
        with patch.object(setup, "_lake") as lake:
            assert setup.install_lean() is True
        lake.assert_not_called()

    def test_declining_the_download_stops(self, toolchain_ready, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path / "absent")
        monkeypatch.setattr("builtins.input", lambda _: "n")
        with patch.object(setup, "_lake") as lake:
            assert setup.install_lean() is False
        lake.assert_not_called()

    def test_runs_the_three_lake_steps_in_order(self, toolchain_ready, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path)
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path / "absent")
        monkeypatch.setattr("builtins.input", lambda _: "y")
        with patch.object(setup, "_lake", return_value=True) as lake:
            assert setup.install_lean() is True
        assert [call.args for call in lake.call_args_list] == [
            ("update",),
            ("exe", "cache", "get"),
            ("build", "Warmup"),
        ]

    def test_a_committed_manifest_is_honoured_not_regenerated(self, toolchain_ready, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path)
        (tmp_path / "lake-manifest.json").write_text("{}")
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path / "absent")
        monkeypatch.setattr("builtins.input", lambda _: "y")
        with patch.object(setup, "_lake", return_value=True) as lake:
            assert setup.install_lean() is True
        assert [call.args for call in lake.call_args_list] == [
            ("exe", "cache", "get"),
            ("build", "Warmup"),
        ]

    def test_without_a_manifest_dependencies_are_resolved_first(self, toolchain_ready, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "LEAN_PROJECT_DIR", tmp_path)
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path / "absent")
        monkeypatch.setattr("builtins.input", lambda _: "y")
        with patch.object(setup, "_lake", return_value=True) as lake:
            assert setup.install_lean() is True
        assert [call.args for call in lake.call_args_list][0] == ("update",)

    def test_a_failing_step_aborts_the_rest(self, toolchain_ready, monkeypatch, tmp_path):
        monkeypatch.setattr(setup, "mathlib_lib", lambda: tmp_path / "absent")
        monkeypatch.setattr("builtins.input", lambda _: "y")
        with patch.object(setup, "_lake", return_value=False) as lake:
            assert setup.install_lean() is False
        assert lake.call_count == 1

    def test_declining_elan_stops_before_lake(self, monkeypatch):
        monkeypatch.setattr(setup, "materialize_lean_project", lambda: True)
        monkeypatch.setattr(setup.toolchain, "which", lambda _: None)
        monkeypatch.setattr("builtins.input", lambda _: "n")
        with patch.object(setup, "_lake") as lake:
            assert setup.install_lean() is False
        lake.assert_not_called()

    def test_an_unusable_toolchain_stops_before_lake(self, monkeypatch):
        monkeypatch.setattr(setup, "materialize_lean_project", lambda: True)
        monkeypatch.setattr(setup, "ensure_elan", lambda: True)
        monkeypatch.setattr(setup, "ensure_toolchain", lambda: False)
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


class TestUnknownEnvKeys:
    """A key nothing reads is a silent misconfiguration — CLAUDE_CLI_CMD sat unused for weeks."""

    def test_recognised_keys_are_not_reported(self, env_path):
        env_path.write_text("LLM_BACKEND=claude-cli\nLLM_MODEL=x\nCLAUDE_CONFIG_DIR=/tmp\n")
        assert setup.unknown_env_keys() == []

    def test_unknown_keys_are_reported_sorted(self, env_path):
        env_path.write_text("LLM_MODEL=x\nZED=1\nCOMPOSE_FILE=y\n")
        assert setup.unknown_env_keys() == ["COMPOSE_FILE", "ZED"]

    def test_a_near_miss_is_caught(self, env_path):
        """CLAUDE_CLI_CMD looks plausible; the code reads LLM_CLI_CMD."""
        env_path.write_text("CLAUDE_CLI_CMD=claude-cf\n")
        assert setup.unknown_env_keys() == ["CLAUDE_CLI_CMD"]

    def test_missing_env_file_is_empty(self, env_path):
        assert setup.unknown_env_keys() == []

    def test_every_key_setup_writes_is_recognised(self, env_path):
        """Whatever setup writes must never show up as unused."""
        written = {
            "LLM_BACKEND",
            "CLAUDE_CONFIG_DIR",
            "LLM_MODEL",
            "PROOF_CACHE_TTL_DAYS",
            "LLM_BASE_URL",
            "LLM_API_KEY",
        }
        assert written <= setup.KNOWN_ENV_KEYS


class TestDocumentedEnvKeys:
    """The README's configuration table and KNOWN_ENV_KEYS must agree.

    They drifted once already: LLM_FAILURE_STREAK was documented and read, but
    absent from KNOWN_ENV_KEYS, so setting it made `formal status` report it as a
    key nothing reads. A wrong warning about your own configuration is worse than
    no warning.
    """

    def _documented(self):
        import pathlib
        import re

        readme = pathlib.Path(__file__).parent.parent / "README.md"
        return set(re.findall(r"^\| `([A-Z_]+)`", readme.read_text(), re.M))

    def test_every_documented_key_is_recognised(self):
        undeclared = sorted(self._documented() - setup.KNOWN_ENV_KEYS)
        assert undeclared == [], f"documented but would be reported as unused: {undeclared}"

    def test_every_recognised_key_is_documented(self):
        undocumented = sorted(setup.KNOWN_ENV_KEYS - self._documented())
        assert undocumented == [], f"read by formal but absent from the README table: {undocumented}"
