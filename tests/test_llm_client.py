"""Tests for llm_client — CLI backend timeouts, retries and error reporting."""

import subprocess
from unittest.mock import patch

import pytest

from formal.llm_client import _call_cli, extract_code_block


def _result(returncode=0, stdout="", stderr=""):
    return subprocess.CompletedProcess(args=[], returncode=returncode, stdout=stdout, stderr=stderr)


class TestTimeout:
    def test_repeated_stalls_become_a_readable_error(self, monkeypatch):
        monkeypatch.setenv("LLM_TIMEOUT", "7")

        def raise_timeout(*args, **kwargs):
            raise subprocess.TimeoutExpired(cmd="claude", timeout=7)

        monkeypatch.setattr(subprocess, "run", raise_timeout)
        with pytest.raises(RuntimeError, match="stalled twice"):
            _call_cli("sys", "user")

    def test_a_stall_is_retried_once_and_can_succeed(self, monkeypatch):
        """Timeouts were observed as outright stalls, so the retry usually lands."""
        monkeypatch.setenv("LLM_TIMEOUT", "7")
        calls = []

        def stall_then_answer(*args, **kwargs):
            calls.append(1)
            if len(calls) == 1:
                raise subprocess.TimeoutExpired(cmd="claude", timeout=7)
            return _result(stdout="recovered")

        monkeypatch.setattr(subprocess, "run", stall_then_answer)
        assert _call_cli("sys", "user") == "recovered"
        assert len(calls) == 2

    def test_the_error_names_the_budget_and_a_remedy(self, monkeypatch):
        monkeypatch.setenv("LLM_TIMEOUT", "7")

        def raise_timeout(*args, **kwargs):
            raise subprocess.TimeoutExpired(cmd="claude", timeout=7)

        monkeypatch.setattr(subprocess, "run", raise_timeout)
        with pytest.raises(RuntimeError) as excinfo:
            _call_cli("sys", "user")
        assert "7s" in str(excinfo.value)
        assert "MAX_PARALLEL_PROPERTIES" in str(excinfo.value)

    def test_a_stall_is_retried_at_most_once(self, monkeypatch):
        monkeypatch.setenv("LLM_TIMEOUT", "7")
        calls = []

        def raise_timeout(*args, **kwargs):
            calls.append(1)
            raise subprocess.TimeoutExpired(cmd="claude", timeout=7)

        monkeypatch.setattr(subprocess, "run", raise_timeout)
        with pytest.raises(RuntimeError):
            _call_cli("sys", "user")
        assert len(calls) == 2

    def test_default_budget_matches_the_pre_container_value(self, monkeypatch):
        monkeypatch.delenv("LLM_TIMEOUT", raising=False)
        seen = {}

        def capture(*args, **kwargs):
            seen["timeout"] = kwargs.get("timeout")
            return _result(stdout="ok")

        monkeypatch.setattr(subprocess, "run", capture)
        _call_cli("sys", "user")
        assert seen["timeout"] == 480


class TestRetries:
    def test_a_failing_exit_code_is_retried_once(self, monkeypatch):
        results = iter([_result(returncode=1, stderr="boom"), _result(stdout="second try")])
        monkeypatch.setattr(subprocess, "run", lambda *a, **k: next(results))
        assert _call_cli("sys", "user") == "second try"

    def test_two_failures_raise_with_the_last_error(self, monkeypatch):
        monkeypatch.setattr(subprocess, "run", lambda *a, **k: _result(returncode=1, stderr="boom"))
        with pytest.raises(RuntimeError, match="boom"):
            _call_cli("sys", "user")

    def test_success_is_not_retried(self, monkeypatch):
        calls = []

        def once(*args, **kwargs):
            calls.append(1)
            return _result(stdout="fine")

        monkeypatch.setattr(subprocess, "run", once)
        assert _call_cli("sys", "user") == "fine"
        assert len(calls) == 1


class TestModelFlag:
    def test_model_is_passed_through(self, monkeypatch):
        seen = {}

        def capture(cmd, *args, **kwargs):
            seen["cmd"] = cmd
            return _result(stdout="ok")

        monkeypatch.setattr(subprocess, "run", capture)
        _call_cli("sys", "user", model="claude-opus-5")
        assert seen["cmd"][-2:] == ["--model", "claude-opus-5"]

    def test_no_model_flag_when_unset(self, monkeypatch):
        seen = {}

        def capture(cmd, *args, **kwargs):
            seen["cmd"] = cmd
            return _result(stdout="ok")

        monkeypatch.setattr(subprocess, "run", capture)
        _call_cli("sys", "user")
        assert "--model" not in seen["cmd"]


class TestExtractCodeBlock:
    def test_extracts_a_fenced_block_by_language(self):
        assert extract_code_block("text\n```lean\ntheorem t : True\n```\n", "lean") == "theorem t : True"

    def test_returns_empty_when_absent(self):
        assert extract_code_block("no fences here", "lean") == ""


class TestCliErrorsSurfaceCleanly:
    def test_runtime_error_becomes_an_exit_code_not_a_traceback(self, monkeypatch, capsys):
        from formal import cli

        monkeypatch.setattr(cli.sys, "argv", ["formal", "verify", "--code", "def f(): pass"])
        monkeypatch.setattr(cli, "_load_env", lambda: None)
        with patch(
            "formal.feature_pipeline.run_feature_pipeline",
            side_effect=RuntimeError("claude did not respond within LLM_TIMEOUT (480s)."),
        ):
            assert cli.main() == 2
        assert "formal: claude did not respond" in capsys.readouterr().err


class TestFencedBlocksContainingFences:
    """Lean that reasons about markdown embeds ``` in string literals.

    An unanchored closing fence truncated such a block mid-literal, and because
    extraction is deterministic every retry reproduced it — the property could
    never recover.
    """

    def _wrap(self, body, lang="lean4"):
        return f"Here you go:\n\n```{lang}\n{body}\n```\n\nThat's it.\n"

    def test_a_fence_inside_a_string_literal_does_not_end_the_block(self):
        body = 'import Mathlib\n\ndef fence : String := "```"\n\ntheorem t : True := trivial'
        extracted = extract_code_block(self._wrap(body), "lean4")
        assert extracted == body
        assert extracted.count('"') % 2 == 0

    def test_the_result_is_not_truncated_mid_literal(self):
        body = 'def fence : String := "```"\ndef after : Nat := 1'
        assert "def after" in extract_code_block(self._wrap(body), "lean4")

    def test_an_ordinary_block_is_unchanged(self):
        body = "import Mathlib\n\ntheorem t : True := trivial"
        assert extract_code_block(self._wrap(body), "lean4") == body

    def test_a_block_at_the_very_start_is_found(self):
        text = "```lean\ntheorem t : True := trivial\n```\n"
        assert extract_code_block(text, "lean") == "theorem t : True := trivial"

    def test_trailing_spaces_after_the_language_are_tolerated(self):
        text = "```lean  \ntheorem t : True := trivial\n```\n"
        assert extract_code_block(text, "lean") == "theorem t : True := trivial"

    def test_the_first_block_still_wins(self):
        text = "```lean\nfirst\n```\n\n```lean\nsecond\n```\n"
        assert extract_code_block(text, "lean") == "first"

    def test_language_agnostic_extraction_is_also_anchored(self):
        body = 'def fence : String := "```"'
        assert extract_code_block(self._wrap(body, lang="")) == body

    def test_no_block_returns_empty(self):
        assert extract_code_block("prose with ``` inline and no block", "lean") == ""
