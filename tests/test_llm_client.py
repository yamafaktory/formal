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


class TestNeutralWorkingDirectory:
    """The CLI loads CLAUDE.md from its cwd; formal's prompts must not inherit a project's."""

    def test_the_cli_does_not_run_in_the_callers_directory(self, monkeypatch, tmp_path):
        import os
        import tempfile

        seen = {}

        def capture(cmd, *args, **kwargs):
            seen["cwd"] = kwargs.get("cwd")
            return _result(stdout="ok")

        monkeypatch.chdir(tmp_path)
        monkeypatch.setattr(subprocess, "run", capture)
        _call_cli("sys", "user")
        assert seen["cwd"] == tempfile.gettempdir()
        assert seen["cwd"] != os.getcwd()


class TestRepeatedFailures:
    """No backend's wording is known — repetition is the signal.

    Continuing does not cost money, refused calls are not billed. It costs truth:
    five modules were reported as having errored properties when they never ran.
    """

    @pytest.fixture(autouse=True)
    def _clean_streak(self, monkeypatch):
        from formal.llm_client import reset_failure_streak

        monkeypatch.setenv("LLM_BACKEND", "claude-cli")
        reset_failure_streak()
        yield
        reset_failure_streak()

    def _failing(self, monkeypatch, messages):
        """Fail one call_llm per message, mocking beneath call_llm's accounting."""
        step = iter(messages)

        def fail(system, user, model=None):
            raise RuntimeError(next(step))

        monkeypatch.setattr("formal.llm_client._call_cli", fail)

    @pytest.mark.parametrize(
        "message",
        [
            "You've hit your individual spend limit · run /usage-credits",
            "model 'llama3' not found, try pulling it first",  # Ollama
            "Error: Failed to connect to LM Studio server",
            "402 Payment Required",
            "something nobody has ever written before",
        ],
    )
    def test_any_repeated_error_stops_the_run(self, monkeypatch, message):
        from formal.llm_client import BackendUnavailable, call_llm

        self._failing(monkeypatch, [message] * 3)
        for _ in range(2):
            with pytest.raises(RuntimeError) as excinfo:
                call_llm("sys", "user")
            assert not isinstance(excinfo.value, BackendUnavailable)
        with pytest.raises(BackendUnavailable, match="will not recover"):
            call_llm("sys", "user")

    def test_differing_errors_never_trip_it(self, monkeypatch):
        from formal.llm_client import BackendUnavailable, call_llm

        self._failing(monkeypatch, [f"transient failure {i}" for i in range(5)])
        for _ in range(5):
            with pytest.raises(RuntimeError) as excinfo:
                call_llm("sys", "user")
            assert not isinstance(excinfo.value, BackendUnavailable)

    def test_a_success_clears_the_streak(self, monkeypatch):
        from formal.llm_client import BackendUnavailable, call_llm

        outcomes = ["same error", "same error", None, "same error"]
        step = iter(outcomes)

        def maybe_fail(system, user, model=None):
            message = next(step)
            if message is None:
                return "fine"
            raise RuntimeError(message)

        monkeypatch.setattr("formal.llm_client._call_cli", maybe_fail)
        for _ in range(2):
            with pytest.raises(RuntimeError):
                call_llm("sys", "user")
        assert call_llm("sys", "user") == "fine"
        with pytest.raises(RuntimeError) as excinfo:
            call_llm("sys", "user")
        assert not isinstance(excinfo.value, BackendUnavailable)

    def test_whitespace_differences_do_not_look_like_new_errors(self, monkeypatch):
        from formal.llm_client import BackendUnavailable, call_llm

        self._failing(monkeypatch, ["spend  limit", "spend limit\n", " spend limit "])
        for _ in range(2):
            with pytest.raises(RuntimeError):
                call_llm("sys", "user")
        with pytest.raises(BackendUnavailable):
            call_llm("sys", "user")

    def test_the_threshold_is_configurable(self, monkeypatch):
        from formal.llm_client import BackendUnavailable, call_llm

        monkeypatch.setenv("LLM_FAILURE_STREAK", "2")
        self._failing(monkeypatch, ["boom"] * 2)
        with pytest.raises(RuntimeError):
            call_llm("sys", "user")
        with pytest.raises(BackendUnavailable):
            call_llm("sys", "user")

    def test_a_refusal_is_a_runtime_error_so_the_cli_reports_it(self):
        from formal.llm_client import BackendUnavailable

        assert issubclass(BackendUnavailable, RuntimeError)


class TestRefusalStopsTheRun:
    """Per-property error handling must not swallow a refusal — that is what kept it going."""

    def _pipeline_with(self, monkeypatch, failing):
        import formal.feature_pipeline as fp
        from formal.feature_extractor import DecomposedFeature, Property, PureFunction

        props = [Property(id=f"prop_{i}", description="d", function="f", kind="bound", formal="") for i in range(3)]
        feature = DecomposedFeature(
            feature_summary="s",
            pure_functions=[PureFunction(name="f", code="def f(): pass", description="f")],
            impure_parts=[],
            properties=[],
        )
        monkeypatch.setattr(fp, "decompose", lambda code, language="Python": feature)
        monkeypatch.setattr(fp, "extract_properties", lambda feature, language="Python": props)
        monkeypatch.setattr(fp, "formalize", failing)
        return fp

    def test_a_refusal_aborts_instead_of_marking_properties_errored(self, monkeypatch):
        from formal.llm_client import BackendUnavailable

        def refuse(prop, fn, language="Python"):
            raise BackendUnavailable("spend limit")

        fp = self._pipeline_with(monkeypatch, refuse)
        with pytest.raises(BackendUnavailable):
            fp.run_feature_pipeline("def f(): pass", parallel=False)

    def test_an_ordinary_error_still_becomes_an_errored_property(self, monkeypatch):
        def blow_up(prop, fn, language="Python"):
            raise ValueError("something else")

        fp = self._pipeline_with(monkeypatch, blow_up)
        result = fp.run_feature_pipeline("def f(): pass", parallel=False)
        assert result.properties_errored == 3
