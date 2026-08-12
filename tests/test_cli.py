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
    def _write(self, tmp_path, body):
        (tmp_path / "src" / "formal").mkdir(parents=True)
        (tmp_path / ".env").write_text(body)
        return str(tmp_path / "src" / "formal" / "cli.py")

    def test_parses_keys_and_strips_quotes(self, tmp_path, monkeypatch):
        monkeypatch.setattr(cli, "__file__", self._write(tmp_path, "A=1\nB=\"two\"\nC='three'\n"))
        for key in ("A", "B", "C"):
            monkeypatch.delenv(key, raising=False)
        cli._load_env()
        assert (cli.os.environ["A"], cli.os.environ["B"], cli.os.environ["C"]) == ("1", "two", "three")

    def test_skips_comments_and_blank_lines(self, tmp_path, monkeypatch):
        monkeypatch.setattr(cli, "__file__", self._write(tmp_path, "# comment\n\nA=1\nnot-a-pair\n"))
        monkeypatch.delenv("A", raising=False)
        cli._load_env()
        assert cli.os.environ["A"] == "1"

    def test_does_not_override_the_real_environment(self, tmp_path, monkeypatch):
        monkeypatch.setattr(cli, "__file__", self._write(tmp_path, "A=from-file\n"))
        monkeypatch.setenv("A", "from-shell")
        cli._load_env()
        assert cli.os.environ["A"] == "from-shell"

    def test_missing_file_is_not_an_error(self, tmp_path, monkeypatch):
        (tmp_path / "src" / "formal").mkdir(parents=True)
        monkeypatch.setattr(cli, "__file__", str(tmp_path / "src" / "formal" / "cli.py"))
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
