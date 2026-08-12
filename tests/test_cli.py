"""Tests for cli — .env parsing, argument validation, exit codes."""

from unittest.mock import patch

import pytest

from formal import cli
from formal.feature_pipeline import FeaturePipelineResult, _detect_language


def _result(found=2, verified=2, unverifiable=0) -> FeaturePipelineResult:
    return FeaturePipelineResult(
        feature_file="x.py",
        feature_summary="a summary",
        pure_functions=["f"],
        impure_parts=[],
        properties_found=found,
        properties_verified=verified,
        properties_unverifiable=unverifiable,
        results=[],
    )


class TestLoadEnv:
    def _env_at(self, tmp_path, monkeypatch, body):
        monkeypatch.setenv("FORMAL_HOME", str(tmp_path))
        (tmp_path / ".env").write_text(body)

    def test_parses_keys_and_strips_quotes(self, tmp_path, monkeypatch):
        self._env_at(tmp_path, monkeypatch, "A=1\nB=\"two\"\nC='three'\n")
        for key in ("A", "B", "C"):
            monkeypatch.delenv(key, raising=False)
        cli._load_env()
        assert (cli.os.environ["A"], cli.os.environ["B"], cli.os.environ["C"]) == ("1", "two", "three")

    def test_skips_comments_and_blank_lines(self, tmp_path, monkeypatch):
        self._env_at(tmp_path, monkeypatch, "# comment\n\nA=1\nnot-a-pair\n")
        monkeypatch.delenv("A", raising=False)
        cli._load_env()
        assert cli.os.environ["A"] == "1"

    def test_does_not_override_the_real_environment(self, tmp_path, monkeypatch):
        self._env_at(tmp_path, monkeypatch, "A=from-file\n")
        monkeypatch.setenv("A", "from-shell")
        cli._load_env()
        assert cli.os.environ["A"] == "from-shell"

    def test_missing_file_is_not_an_error(self, tmp_path, monkeypatch):
        monkeypatch.setenv("FORMAL_HOME", str(tmp_path))
        cli._load_env()


class TestArgumentValidation:
    def test_verify_without_file_or_code_exits(self, monkeypatch):
        monkeypatch.setattr(cli.sys, "argv", ["formal", "verify"])
        monkeypatch.setattr(cli, "_load_env", lambda: None)
        with pytest.raises(SystemExit):
            cli.main()

    def test_verify_with_both_file_and_code_exits(self, monkeypatch):
        monkeypatch.setattr(cli.sys, "argv", ["formal", "verify", "x.py", "--code", "def f(): pass"])
        monkeypatch.setattr(cli, "_load_env", lambda: None)
        with pytest.raises(SystemExit):
            cli.main()


class TestVerifyExitCode:
    def test_missing_file_returns_2(self, monkeypatch, capsys):
        monkeypatch.setattr(cli.sys, "argv", ["formal", "verify", "/nope/missing.py"])
        monkeypatch.setattr(cli, "_load_env", lambda: None)
        assert cli.main() == 2
        assert "no such file" in capsys.readouterr().err

    @pytest.mark.parametrize(
        ("found", "verified", "unverifiable", "expected"),
        [(2, 2, 0, 0), (0, 0, 0, 0), (2, 1, 0, 1), (2, 0, 0, 1)],
    )
    def test_exit_code_follows_score(self, monkeypatch, found, verified, unverifiable, expected):
        monkeypatch.setattr(cli.sys, "argv", ["formal", "verify", "--code", "def f(): pass"])
        monkeypatch.setattr(cli, "_load_env", lambda: None)
        with patch(
            "formal.feature_pipeline.run_feature_pipeline",
            return_value=_result(found, verified, unverifiable),
        ):
            assert cli.main() == expected

    def test_json_output_is_parseable(self, monkeypatch, capsys):
        monkeypatch.setattr(cli.sys, "argv", ["formal", "verify", "--code", "def f(): pass", "--json"])
        monkeypatch.setattr(cli, "_load_env", lambda: None)
        with patch("formal.feature_pipeline.run_feature_pipeline", return_value=_result()):
            cli.main()
        payload = cli.json.loads(capsys.readouterr().out)
        assert payload["overall_score"] == "full"
        assert payload["properties_verified"] == 2


class TestLanguageDetection:
    @pytest.mark.parametrize(
        ("suffix", "language"),
        [
            (".zig", "Zig"),
            (".c", "C"),
            (".h", "C"),
            (".mjs", "JavaScript"),
            (".kts", "Kotlin"),
            (".cc", "C++"),
            (".PY", "Python"),
            (".unknown", "unknown"),
        ],
    )
    def test_detects_language_from_suffix(self, suffix, language):
        assert _detect_language(suffix) == language


class TestErrorExitCode:
    def _errored(self):
        from formal.property_verifier import PropertyResult

        return FeaturePipelineResult(
            feature_file="mod.py",
            feature_summary="a module",
            pure_functions=["f"],
            impure_parts=[],
            properties_found=1,
            properties_verified=0,
            properties_unverifiable=0,
            results=[
                PropertyResult(
                    property_id="p0",
                    description="d",
                    kind="bound",
                    function="f",
                    verified=False,
                    lean_code="",
                    lean_output="",
                    retries=0,
                    reason="NameError: boom",
                    status="error",
                    preconditions=[],
                    assumptions=[],
                )
            ],
        )

    def test_a_tool_failure_exits_2_not_1(self, monkeypatch):
        """Exit 1 means 'your code is wrong'; a crash must not claim that."""
        monkeypatch.setattr(cli.sys, "argv", ["formal", "verify", "--code", "def f(): pass"])
        monkeypatch.setattr(cli, "_load_env", lambda: None)
        with patch("formal.feature_pipeline.run_feature_pipeline", return_value=self._errored()):
            assert cli.main() == 2

    def test_json_reports_the_error_count(self, monkeypatch, capsys):
        monkeypatch.setattr(cli.sys, "argv", ["formal", "verify", "--code", "def f(): pass", "--json"])
        monkeypatch.setattr(cli, "_load_env", lambda: None)
        with patch("formal.feature_pipeline.run_feature_pipeline", return_value=self._errored()):
            cli.main()
        payload = cli.json.loads(capsys.readouterr().out)
        assert payload["properties_errored"] == 1
        assert payload["overall_score"] == "error"
