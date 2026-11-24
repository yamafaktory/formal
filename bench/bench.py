# /// script
# requires-python = ">=3.11"
# ///
import argparse
import json
import os
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
import tomllib
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

BENCH = Path(__file__).resolve().parent
ROOT = BENCH.parent
HIDDEN = BENCH / "hidden"
VENDOR = BENCH / "vendor"
LEAN_PROJECT = ROOT / "lean_project"
LEAN_METADATA = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
FORMAL = ROOT / "rust" / "target" / "release" / "formal"
HOME = Path.home()
CARGO_TARGET = Path(tempfile.gettempdir()) / "formal-bench-target"
CLAUDE = "claude"
TIME_LIMIT = 20 * 60
SERVER_START = 120
MODEL = "claude-opus-5-5"
ARMS = ("lean", "formal")
TOOLS = "Bash,Read,Write,Edit,Glob,Grep"
VERDICTS = ("verified", "refuted", "unknown")
GRADES = ("right", "wrong verified", "wrong refuted", "no claim", "error")
PATH = "/usr/local/bin:/usr/bin"
RUNNING: set[subprocess.Popen] = set()
RUNNING_LOCK = threading.Lock()

TASK = """\
Check one function against one property, and back your verdict with Lean 4.

The code is in this directory. The function is {function}.

The property: {property}

Decide whether the code as written satisfies the property.

- When you prove in Lean that it does, your verdict is "verified".
- When you find an input on which the code breaks the property, your verdict is "refuted".
- Otherwise, your verdict is "unknown".

{tools}

When you are done, write `answer.json` in this directory:

{{"verdict": "verified", "evidence": "..."}}

The verdict is "verified", "refuted" or "unknown". The evidence is the path of your Lean proof, the input that breaks the property, or the reason you have neither.
"""

LEAN_TOOLS = (
    "Lean 4 and Mathlib are set up in `{lean_project}`. "
    "To check a Lean file, run `lake env lean <file>` from that directory."
)

FORMAL_TOOLS = (
    "formal checks Lean proofs for you, and it runs at http://127.0.0.1:{port}. "
    "Run `curl -s localhost:{port}/guide` and follow the workflow it returns."
)


@dataclass(frozen=True)
class Task:
    id: str
    language: str
    files: tuple[str, ...]
    function: str
    property: str


def tasks() -> list[Task]:
    table = tomllib.loads((BENCH / "tasks.toml").read_text())
    return [Task(**{**entry, "files": tuple(entry["files"])}) for entry in table["task"]]


def seeds() -> dict[str, dict[str, str]]:
    return tomllib.loads((HIDDEN / "seeds.toml").read_text())


def seeded(text: str, seed: dict[str, str]) -> str:
    found = text.count(seed["find"])
    if found != 1:
        raise ValueError(f"the seed for {seed['file']} matches {found} times, not once")
    return text.replace(seed["find"], seed["replace"])


def prepare(task: Task, seed: dict[str, str] | None, work: Path) -> None:
    work.mkdir(parents=True, exist_ok=True)
    for name in task.files:
        source = VENDOR / name
        if source.is_dir():
            shutil.copytree(source, work / source.name, dirs_exist_ok=True)
        else:
            shutil.copy2(source, work / source.name)
    if seed is not None:
        target = work / seed["file"]
        target.write_text(seeded(target.read_text(), seed))


def prompt(task: Task, arm: str, lean_project: Path, port: int) -> str:
    tools = LEAN_TOOLS.format(lean_project=lean_project)
    if arm == "formal":
        tools = f"{tools}\n\n{FORMAL_TOOLS.format(port=port)}"
    return TASK.format(function=task.function, property=task.property, tools=tools)


def confined(environment: dict[str, str], binds: list[tuple[str, Path, Path]]) -> list[str]:
    argv = [
        "bwrap", "--die-with-parent", "--new-session", "--unshare-pid", "--clearenv",
        "--ro-bind", "/usr", "/usr", "--ro-bind", "/etc", "/etc", "--ro-bind", "/opt", "/opt",
        "--symlink", "usr/lib", "/lib", "--symlink", "usr/lib64", "/lib64",
        "--symlink", "usr/bin", "/bin", "--symlink", "usr/sbin", "/sbin",
        "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp", "--tmpfs", "/run",
        "--tmpfs", str(HOME),
    ]
    for name, value in {"HOME": str(HOME), "PATH": PATH, "LANG": "C.UTF-8", **environment}.items():
        argv += ["--setenv", name, value]
    for kind, source, target in binds:
        argv += [kind, str(source), str(target)]
    return argv


def toolchains() -> list[tuple[str, Path, Path]]:
    return [("--ro-bind-try", HOME / name, HOME / name) for name in (".elan", ".rustup")]


def agent_sandbox(run: Path) -> list[str]:
    agent = run / "agent"
    binds = [
        *toolchains(),
        ("--bind", agent, agent),
        ("--ro-bind", LEAN_PROJECT / ".lake" / "packages", agent / "lean" / ".lake" / "packages"),
        ("--bind", agent / "home" / ".claude", HOME / ".claude"),
        ("--bind-try", HOME / ".claude" / ".credentials.json", HOME / ".claude" / ".credentials.json"),
        ("--bind", agent / "home" / ".claude.json", HOME / ".claude.json"),
    ]
    return confined({"TERM": "dumb"}, binds) + ["--chdir", str(agent / "work")]


def formal_sandbox(run: Path, port: int) -> list[str]:
    agent, server = run / "agent", run / "formal"
    environment = {
        "FORMAL_HOME": str(server / "home"),
        "LEAN_PROJECT_DIR": str(server / "lean"),
        "FORMAL_PORT": str(port),
    }
    binds = [
        *toolchains(),
        ("--bind", server, server),
        ("--ro-bind", LEAN_PROJECT / ".lake" / "packages", server / "lean" / ".lake" / "packages"),
        ("--ro-bind", FORMAL, server / "formal"),
        ("--ro-bind", agent / "work", agent / "work"),
        ("--ro-bind", agent / "lean", agent / "lean"),
    ]
    return confined(environment, binds) + [str(server / "formal"), "serve"]


def command(task: Task, arm: str, model: str, effort: str | None, run: Path, port: int) -> list[str]:
    agent = [
        CLAUDE, "-p", prompt(task, arm, run / "agent" / "lean", port), "--safe-mode",
        "--no-session-persistence", "--output-format", "stream-json", "--verbose",
        "--model", model, "--tools", TOOLS, "--dangerously-skip-permissions",
    ]
    if effort is not None:
        agent += ["--effort", effort]
    return agent_sandbox(run) + agent


def hidden_test(task: Task, work: Path) -> list[str]:
    match task.language:
        case "python":
            test = HIDDEN / "python" / f"test_{task.id.replace('-', '_')}.py"
            return [
                "uv", "run", "--quiet", "--locked", "--project", str(HIDDEN / "python"),
                "pytest", "-q", "-p", "no:cacheprovider", str(test),
            ]
        case "rust":
            crate = work.parent / "check"
            shutil.copytree(HIDDEN / "rust", crate)
            return [
                "cargo", "test", "--quiet", "--locked", "--manifest-path", str(crate / "Cargo.toml"),
                "--test", task.id.replace("-", "_"),
            ]
        case "typescript":
            return ["node", "--test", str(HIDDEN / "typescript" / f"{task.id}.test.ts")]
    raise ValueError(f"no hidden test runs {task.language}")


def holds(task: Task, seed: dict[str, str] | None, scratch: Path) -> bool:
    work = scratch / "work"
    shutil.rmtree(scratch, ignore_errors=True)
    prepare(task, seed, work)
    env = {
        **os.environ,
        "BENCH_WORK": str(work),
        "CARGO_TARGET_DIR": str(CARGO_TARGET),
        "PROPTEST_CASES": "1000",
    }
    done = subprocess.run(hidden_test(task, work), cwd=HIDDEN / task.language, env=env, capture_output=True)
    return done.returncode == 0


def problems(task: Task, planted: dict, scratch: Path) -> list[str]:
    found = []
    if not holds(task, None, scratch / task.id / "original"):
        found.append(f"{task.id}: the hidden test fails on the original code")
    if task.id in planted and holds(task, planted[task.id], scratch / task.id / "seeded"):
        found.append(f"{task.id}: the hidden test passes on the seeded code")
    return found


def verify(chosen: list[Task]) -> list[str]:
    planted = seeds()
    with tempfile.TemporaryDirectory(prefix="formal-bench-check-") as scratch:
        return [problem for task in chosen for problem in problems(task, planted, Path(scratch))]


def grade(verdict: str | None, held: bool) -> str:
    match verdict:
        case "verified":
            return "right" if held else "wrong verified"
        case "refuted":
            return "wrong refuted" if held else "right"
    return "no claim"


def read_answer(answer: Path) -> tuple[str | None, str | None]:
    try:
        content = json.loads(answer.read_text())
        verdict, evidence = content.get("verdict"), content.get("evidence")
    except (OSError, ValueError, AttributeError):
        return None, None
    if verdict not in VERDICTS:
        return None, None
    return verdict, evidence if isinstance(evidence, str) else None


def events(output: str) -> list[dict]:
    found = []
    for line in output.splitlines():
        try:
            event = json.loads(line)
        except ValueError:
            continue
        if isinstance(event, dict):
            found.append(event)
    return found


def usage(output: str) -> dict:
    stream = events(output)
    result = next((event for event in reversed(stream) if event.get("type") == "result"), None)
    if result is not None:
        models = result.get("modelUsage", {})
        return {
            "tokens": sum(
                model.get(key, 0)
                for model in models.values()
                for key in ("inputTokens", "outputTokens", "cacheReadInputTokens", "cacheCreationInputTokens")
            ),
            "output_tokens": sum(model.get("outputTokens", 0) for model in models.values()),
            "cost": result.get("total_cost_usd"),
            "models": sorted(models),
            "error": bool(result.get("is_error")),
            "subtype": result.get("subtype"),
        }
    messages = [
        event["message"]
        for event in stream
        if event.get("type") == "assistant" and isinstance(event.get("message"), dict)
    ]
    counted = [message.get("usage", {}) for message in messages]
    return {
        "tokens": sum(
            part.get(key, 0)
            for part in counted
            for key in ("input_tokens", "output_tokens", "cache_read_input_tokens", "cache_creation_input_tokens")
        ),
        "output_tokens": sum(part.get("output_tokens", 0) for part in counted),
        "cost": None,
        "models": sorted({message["model"] for message in messages if "model" in message}),
        "error": False,
        "subtype": None,
    }


@dataclass(frozen=True)
class Setup:
    model: str
    effort: str | None
    claude: str
    formal: str
    commit: str


@dataclass(frozen=True)
class Outcome:
    output: str
    returncode: int | None
    timed_out: bool
    seconds: float


def record(task: Task, arm: str, number: int, setup: Setup, held: bool, outcome: Outcome, answer: Path) -> dict:
    spent = usage(outcome.output)
    failed = not outcome.timed_out and (outcome.returncode != 0 or spent["error"])
    verdict, evidence = (None, None) if outcome.timed_out or failed else read_answer(answer)
    return {
        "task": task.id,
        "arm": arm,
        "run": number,
        "model": setup.model,
        "effort": setup.effort,
        "models": spent["models"],
        "claude": setup.claude,
        "formal": setup.formal,
        "commit": setup.commit,
        "verdict": verdict,
        "evidence": evidence,
        "holds": held,
        "grade": "error" if failed else grade(verdict, held),
        "seconds": round(outcome.seconds, 1),
        "tokens": spent["tokens"],
        "output_tokens": spent["output_tokens"],
        "cost": spent["cost"],
        "timed_out": outcome.timed_out,
        "returncode": outcome.returncode,
        "subtype": spent["subtype"],
    }


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def start(run: Path) -> None:
    for name in ("agent/work", "agent/lean/.lake/packages", "agent/home/.claude", "formal/home", "formal/lean/.lake/packages"):
        (run / name).mkdir(parents=True, exist_ok=True)
    for project in ("agent/lean", "formal/lean"):
        for name in LEAN_METADATA:
            shutil.copy2(LEAN_PROJECT / name, run / project / name)
    (run / "agent" / "home" / ".claude" / ".credentials.json").touch()
    (run / "formal" / "formal").touch()
    shutil.copy2(HOME / ".claude.json", run / "agent" / "home" / ".claude.json")


def spawn(argv: list[str], **options) -> subprocess.Popen:
    process = subprocess.Popen(argv, start_new_session=True, **options)
    with RUNNING_LOCK:
        RUNNING.add(process)
    return process


def stop(process: subprocess.Popen) -> None:
    with RUNNING_LOCK:
        RUNNING.discard(process)
    if process.poll() is None:
        os.killpg(process.pid, signal.SIGKILL)
    process.wait()


def stop_all() -> None:
    with RUNNING_LOCK:
        running = list(RUNNING)
    for process in running:
        stop(process)


def serving(port: int, server: subprocess.Popen) -> None:
    deadline = time.monotonic() + SERVER_START
    while time.monotonic() < deadline and server.poll() is None:
        try:
            urllib.request.urlopen(f"http://127.0.0.1:{port}/guide", timeout=1).close()
            return
        except OSError:
            time.sleep(0.5)
    raise OSError(f"formal did not answer on port {port}")


def agent(argv: list[str], work: Path) -> tuple[Outcome, str]:
    process = spawn(argv, cwd=work, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    started = time.monotonic()
    try:
        output, errors = process.communicate(timeout=TIME_LIMIT)
        timed_out = False
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        output, errors = process.communicate()
        timed_out = True
    finally:
        stop(process)
    seconds = time.monotonic() - started
    return Outcome(output, None if timed_out else process.returncode, timed_out, seconds), errors


def run_once(task: Task, seed: dict | None, arm: str, number: int, setup: Setup, out: Path) -> dict:
    kept = out / "runs" / task.id / arm / str(number)
    shutil.rmtree(kept, ignore_errors=True)
    with tempfile.TemporaryDirectory(prefix="formal-bench-") as scratch:
        run = Path(scratch)
        start(run)
        work = run / "agent" / "work"
        prepare(task, seed, work)
        port = free_port()
        server = None
        try:
            if arm == "formal":
                server = spawn(formal_sandbox(run, port), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                serving(port, server)
            outcome, errors = agent(command(task, arm, setup.model, setup.effort, run, port), work)
        finally:
            if server is not None:
                stop(server)
        result = record(task, arm, number, setup, seed is None, outcome, work / "answer.json")
        shutil.copytree(run / "agent", kept / "agent", symlinks=True, ignore=shutil.ignore_patterns("home", ".lake"))
        (kept / "claude.jsonl").write_text(outcome.output)
        (kept / "claude.stderr").write_text(errors)
    return result


def records(out: Path) -> list[dict]:
    path = out / "records.jsonl"
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def mean(values: list) -> float | None:
    known = [value for value in values if value is not None]
    return sum(known) / len(known) if known else None


def summary(every: list[dict]) -> dict[str, dict]:
    table = {}
    for arm in ARMS:
        mine = [entry for entry in every if entry["arm"] == arm]
        if not mine:
            continue
        grades = [entry["grade"] for entry in mine]
        counted = [entry for entry in mine if entry["grade"] != "error"]
        table[arm] = {
            "runs": len(mine),
            **{name: grades.count(name) for name in GRADES},
            "tokens": mean([entry["tokens"] for entry in counted]),
            "seconds": mean([entry["seconds"] for entry in counted]),
            "cost": sum(entry["cost"] or 0 for entry in mine),
        }
    return table


def splits(every: list[dict]) -> list[str]:
    rates: dict[str, dict[str, list[bool]]] = {}
    for entry in every:
        if entry["grade"] != "error":
            rates.setdefault(entry["task"], {}).setdefault(entry["arm"], []).append(entry["grade"] == "right")
    return sorted(
        task
        for task, arms in rates.items()
        if len(arms) == len(ARMS) and len({sum(right) / len(right) for right in arms.values()}) > 1
    )


def chosen_tasks(only: list[str] | None) -> list[Task]:
    every = tasks()
    if not only:
        return every
    unknown = set(only) - {task.id for task in every}
    if unknown:
        sys.exit(f"no such task: {', '.join(sorted(unknown))}")
    return [task for task in every if task.id in only]


def output_of(argv: list[str], cwd: Path = ROOT) -> str:
    return subprocess.run(argv, cwd=cwd, capture_output=True, text=True).stdout.strip()


def setup_of(model: str, effort: str | None) -> Setup:
    dirty = output_of(["git", "status", "--porcelain", "--", "bench"]) != ""
    return Setup(
        model=model,
        effort=effort,
        claude=output_of([CLAUDE, "--version"]),
        formal=output_of([str(FORMAL), "--version"]),
        commit=output_of(["git", "rev-parse", "HEAD"]) + ("+dirty" if dirty else ""),
    )


def check(arguments: argparse.Namespace) -> None:
    found = verify(chosen_tasks(arguments.only))
    for problem in found:
        print(problem)
    if found:
        sys.exit("the hidden tests disagree with the seeds")
    print("every hidden test passes on its original code and fails on its seeded code")


def run(arguments: argparse.Namespace) -> None:
    out = Path(arguments.out)
    out.mkdir(parents=True, exist_ok=True)
    chosen = chosen_tasks(arguments.only)
    found = verify(chosen)
    if found:
        sys.exit("\n".join([*found, "the hidden tests disagree with the seeds: run check"]))
    subprocess.run(["cargo", "build", "--release", "--quiet", "-p", "formal-cli"], cwd=ROOT / "rust", check=True)
    setup = setup_of(arguments.model, arguments.effort)
    planted = seeds()
    done = records(out)
    plan = []
    for task in chosen:
        for arm in arguments.arms:
            first = 1 + sum(1 for entry in done if entry["task"] == task.id and entry["arm"] == arm)
            plan += [(task, arm, number) for number in range(first, first + arguments.runs)]
    pool = ThreadPoolExecutor(arguments.jobs)
    try:
        with (out / "records.jsonl").open("a") as log:
            jobs = {
                pool.submit(run_once, task, planted.get(task.id), arm, number, setup, out): (task, arm, number)
                for task, arm, number in plan
            }
            for job in as_completed(jobs):
                task, arm, number = jobs[job]
                try:
                    entry = job.result()
                except (OSError, subprocess.SubprocessError) as failure:
                    print(f"{task.id:18} {arm:6} #{number} not run: {failure}")
                    continue
                log.write(json.dumps(entry) + "\n")
                log.flush()
                print(f"{task.id:18} {arm:6} #{number} {entry['grade']}")
    except KeyboardInterrupt:
        pool.shutdown(wait=False, cancel_futures=True)
        stop_all()
        sys.exit("interrupted: the runs in progress are stopped and not recorded")
    pool.shutdown()


def cell(value) -> str:
    if value is None:
        return "-"
    return f"{value:.3g}" if isinstance(value, float) and value < 10 else f"{value:.0f}"


def report(arguments: argparse.Namespace) -> None:
    every = records(Path(arguments.out))
    columns = ["runs", *GRADES, "tokens", "seconds", "cost"]
    print("| arm | " + " | ".join(columns) + " |")
    print("|---" * (len(columns) + 1) + "|")
    for arm, row in summary(every).items():
        print(f"| {arm} | " + " | ".join(cell(row[column]) for column in columns) + " |")
    disagree = splits(every)
    print("\nTasks where the arms disagree: " + (", ".join(disagree) if disagree else "none"))


def main() -> None:
    shared = argparse.ArgumentParser(add_help=False)
    shared.add_argument("--out", default=str(BENCH / "results"))
    parser = argparse.ArgumentParser(description="Measure what formal adds to an agent that writes Lean.")
    commands = parser.add_subparsers(required=True)
    checking = commands.add_parser("check", parents=[shared], help="check each hidden test on the original and the seeded code")
    checking.add_argument("--only", nargs="*")
    checking.set_defaults(command=check)
    running = commands.add_parser("run", parents=[shared], help="run the agent on the tasks, in both arms")
    running.add_argument("--only", nargs="*")
    running.add_argument("--arms", nargs="+", choices=ARMS, default=list(ARMS))
    running.add_argument("--runs", type=int, default=3)
    running.add_argument("--jobs", type=int, default=1)
    running.add_argument("--model", default=MODEL)
    running.add_argument("--effort")
    running.set_defaults(command=run)
    reporting = commands.add_parser("report", parents=[shared], help="print the table of the recorded runs")
    reporting.set_defaults(command=report)
    arguments = parser.parse_args()
    arguments.command(arguments)


if __name__ == "__main__":
    main()
