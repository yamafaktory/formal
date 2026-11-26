import json
import shutil
import subprocess
from pathlib import Path

import pytest

import bench


def entry(task, arm, grade, tokens=100, seconds=10.0, cost=0.5, turns=4):
    return {
        "task": task, "arm": arm, "grade": grade, "tokens": tokens, "seconds": seconds, "cost": cost, "turns": turns,
    }


def result(**fields):
    return json.dumps({"type": "result", "is_error": False, "subtype": "success", **fields})


def test_a_seed_replaces_its_text_once():
    seed = {"file": "f.py", "find": "a < b", "replace": "a <= b"}
    assert bench.seeded("if a < b:", seed) == "if a <= b:"


@pytest.mark.parametrize("text", ["no match", "a < b and a < b"])
def test_a_seed_that_does_not_match_exactly_once_is_refused(text):
    with pytest.raises(ValueError):
        bench.seeded(text, {"file": "f.py", "find": "a < b", "replace": "a <= b"})


def test_every_seed_applies_to_its_task_s_code(tmp_path):
    tasks = {task.id: task for task in bench.tasks()}
    for task_id, seed in bench.seeds().items():
        bench.prepare(tasks[task_id], seed, tmp_path / task_id)


@pytest.mark.parametrize(
    ("verdict", "held", "grade"),
    [
        ("verified", True, "right"),
        ("verified", False, "wrong verified"),
        ("refuted", False, "right"),
        ("refuted", True, "wrong refuted"),
        ("unknown", True, "no claim"),
        (None, False, "no claim"),
    ],
)
def test_a_verdict_is_graded_against_the_hidden_test(verdict, held, grade):
    assert bench.grade(verdict, held) == grade


def test_an_answer_outside_the_three_verdicts_is_no_claim(tmp_path):
    answer = tmp_path / "answer.json"
    assert bench.read_answer(answer) == (None, None)
    answer.write_text("not json")
    assert bench.read_answer(answer) == (None, None)
    answer.write_text(json.dumps({"verdict": "proved"}))
    assert bench.read_answer(answer) == (None, None)
    answer.write_text(json.dumps({"verdict": "refuted", "evidence": "x = 3"}))
    assert bench.read_answer(answer) == ("refuted", "x = 3")


def test_usage_comes_from_the_result_when_the_run_ends():
    output = "\n".join(
        [
            json.dumps({"type": "system"}),
            result(
                total_cost_usd=1.25,
                num_turns=6,
                modelUsage={
                    "a": {"inputTokens": 1, "outputTokens": 2, "cacheReadInputTokens": 3, "cacheCreationInputTokens": 4},
                    "b": {"inputTokens": 10, "outputTokens": 20},
                },
            ),
        ]
    )
    spent = bench.usage(output)
    assert (spent["tokens"], spent["output_tokens"], spent["cost"], spent["models"]) == (40, 22, 1.25, ["a", "b"])
    assert spent["turns"] == 6


def test_usage_adds_the_messages_of_a_run_cut_before_its_result():
    message = {"type": "assistant", "message": {"model": "m", "usage": {"input_tokens": 5, "output_tokens": 7}}}
    output = json.dumps(message) + "\n" + json.dumps(message) + "\n{\"type\": \"assist"
    spent = bench.usage(output)
    assert (spent["tokens"], spent["output_tokens"], spent["cost"], spent["models"]) == (24, 14, None, ["m"])


SETUP = bench.Setup(model="m", effort=None, claude="v", formal="f", commit="c")


def run_record(tmp_path, output, returncode=0, timed_out=False, held=False):
    answer = tmp_path / "answer.json"
    answer.write_text(json.dumps({"verdict": "verified", "evidence": "Proof.lean"}))
    outcome = bench.Outcome(output, returncode, timed_out, 3.0)
    return bench.record(bench.tasks()[0], "lean", 1, SETUP, held, outcome, answer)


def test_a_finished_run_is_graded_from_its_answer(tmp_path):
    finished = run_record(tmp_path, result(total_cost_usd=0.5, modelUsage={}))
    assert (finished["verdict"], finished["evidence"], finished["grade"]) == ("verified", "Proof.lean", "wrong verified")
    assert (finished["claude"], finished["formal"], finished["commit"]) == ("v", "f", "c")


def test_a_run_cut_at_the_limit_makes_no_claim_and_keeps_its_tokens(tmp_path):
    message = {"type": "assistant", "message": {"model": "m", "usage": {"output_tokens": 9}}}
    cut = run_record(tmp_path, json.dumps(message), returncode=None, timed_out=True)
    assert (cut["verdict"], cut["grade"], cut["tokens"]) == (None, "no claim", 9)


@pytest.mark.parametrize(
    ("output", "returncode"),
    [(result(is_error=True, subtype="error_during_execution"), 0), ("", 1)],
)
def test_a_run_the_agent_could_not_finish_is_an_error(tmp_path, output, returncode):
    assert run_record(tmp_path, output, returncode=returncode)["grade"] == "error"


def test_the_summary_counts_each_grade_per_arm_and_leaves_errors_out_of_the_means():
    table = bench.summary(
        [
            entry("t", "lean", "wrong verified", tokens=100, seconds=10, turns=6),
            entry("t", "lean", "right", tokens=300, seconds=30, turns=8),
            entry("t", "lean", "error", tokens=0, seconds=1, cost=None, turns=None),
            entry("t", "formal", "wrong verified"),
        ]
    )
    assert table["lean"] == {
        "runs": 3,
        "right": 1,
        "wrong verified": 1,
        "wrong refuted": 0,
        "no claim": 0,
        "error": 1,
        "tokens": 200,
        "seconds": 20,
        "turns": 7,
        "cost": 1.0,
        "cost per right": 1.0,
    }
    assert table["formal"]["runs"] == 1
    assert table["formal"]["cost per right"] is None


def test_a_record_from_before_turns_were_kept_counts_without_them():
    old = entry("t", "lean", "right")
    del old["turns"]
    table = bench.summary([old])
    assert (table["lean"]["turns"], table["lean"]["tokens"]) == (None, 100)


def test_a_task_splits_when_its_arms_are_right_at_different_rates():
    entries = [
        entry("same", "lean", "right"),
        entry("same", "formal", "right"),
        entry("same", "formal", "error"),
        entry("split", "lean", "wrong verified"),
        entry("split", "formal", "right"),
        entry("one-arm", "lean", "right"),
    ]
    assert bench.splits(entries) == ["split"]


def test_only_the_formal_arm_is_told_about_formal():
    task = bench.tasks()[0]
    lean = bench.prompt(task, "lean", Path("/tmp/run/lean"))
    formal = bench.prompt(task, "formal", Path("/tmp/run/lean"))
    assert task.property in lean
    assert "formal" not in lean
    assert "run `formal check <spec>`" in formal
    assert lean.split("\n\n")[:4] == formal.split("\n\n")[:4]


def binds(argv):
    return [(argv[i + 1], argv[i + 2]) for i, word in enumerate(argv) if word.startswith(("--bind", "--ro-bind"))]


def from_repository(argv):
    return sorted(source for source, _ in binds(argv) if source.startswith(str(bench.ROOT)))


def test_the_agent_sees_its_run_and_only_mathlib_from_the_repository():
    run = Path("/tmp/formal-bench-x")
    argv = bench.command(bench.tasks()[0], "lean", "m", "high", run)
    assert (str(run / "agent"), str(run / "agent")) in binds(argv)
    assert from_repository(argv) == [str(bench.LEAN_PROJECT / ".lake" / "packages")]
    assert "--clearenv" in argv
    assert "FORMAL_HOME" not in argv
    assert argv[argv.index("--chdir") + 1] == str(run / "agent" / "work")
    assert argv[-2:] == ["--effort", "high"]


def test_the_formal_arm_also_sees_formal_and_only_formal():
    run = Path("/tmp/formal-bench-x")
    argv = bench.command(bench.tasks()[0], "formal", "m", None, run)
    assert from_repository(argv) == sorted([str(bench.LEAN_PROJECT / ".lake" / "packages"), str(bench.FORMAL)])
    assert (str(bench.FORMAL), str(run / "agent" / "bin" / "formal")) in binds(argv)
    assert argv[argv.index("LEAN_PROJECT_DIR") + 1] == str(run / "agent" / "lean")
    assert argv[argv.index("FORMAL_HOME") + 1].startswith(str(run / "agent"))
    assert argv[argv.index("FORMAL_SANDBOX") + 1] == "off"
    assert argv[argv.index("PATH") + 1].startswith(str(run / "agent" / "bin") + ":")


needs_bwrap = pytest.mark.skipif(
    shutil.which("bwrap") is None or not (bench.HOME / ".claude.json").exists(), reason="needs bwrap and a Claude login"
)


@needs_bwrap
def test_inside_the_agent_sandbox_the_repository_is_gone_and_the_tools_work(tmp_path):
    bench.start(tmp_path)
    script = " && ".join(
        [
            f"test ! -e {bench.ROOT}",
            f"test ! -e {bench.HIDDEN / 'seeds.toml'}",
            "python3 -c 'import random, statistics'",
            'test -z "$CLAUDECODE"',
            *(["cargo --version"] if (bench.HOME / ".rustup").exists() else []),
        ]
    )
    done = subprocess.run(bench.agent_sandbox(tmp_path, "lean") + ["sh", "-c", script], capture_output=True, text=True)
    assert done.returncode == 0, done.stderr


@needs_bwrap
@pytest.mark.skipif(not bench.FORMAL.exists(), reason="needs a release build of formal")
def test_inside_the_formal_arm_s_sandbox_formal_runs_and_the_seeds_are_gone(tmp_path):
    bench.start(tmp_path)
    script = f"formal --version && test ! -e {bench.HIDDEN / 'seeds.toml'}"
    done = subprocess.run(bench.agent_sandbox(tmp_path, "formal") + ["sh", "-c", script], capture_output=True, text=True)
    assert done.returncode == 0, done.stderr


def test_a_run_keeps_its_files_and_records_its_answer(tmp_path, monkeypatch):
    stub = tmp_path / "claude"
    stub.write_text(
        "#!/bin/sh\n"
        "echo '{\"verdict\": \"refuted\", \"evidence\": \"x = 1\"}' > answer.json\n"
        "echo 'no output on stderr' >&2\n"
        f"echo '{result(total_cost_usd=0.25, modelUsage={'m': {'outputTokens': 3}})}'\n"
    )
    stub.chmod(0o755)
    monkeypatch.setattr(bench, "CLAUDE", str(stub))
    monkeypatch.setattr(bench, "agent_sandbox", lambda run, arm: [])
    task = next(task for task in bench.tasks() if task.id in bench.seeds())
    entry_ = bench.run_once(task, bench.seeds()[task.id], "lean", 1, SETUP, tmp_path / "out")
    assert (entry_["verdict"], entry_["grade"], entry_["cost"], entry_["output_tokens"]) == ("refuted", "right", 0.25, 3)
    kept = tmp_path / "out" / "runs" / task.id / "lean" / "1"
    assert (kept / "agent" / "work" / "answer.json").exists()
    assert (kept / "agent" / "lean" / "lakefile.toml").exists()
    assert not (kept / "agent" / "home").exists()
    assert (kept / "claude.stderr").read_text() == "no output on stderr\n"
