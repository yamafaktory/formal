import json
import os
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import hints, sandbox, toolchain
from .paths import LEAN_PROJECT_DIR

LEAN_TIMEOUT = int(os.getenv("LEAN_TIMEOUT", "120"))
AUTO_TACTIC_TIMEOUT = 20  # seconds for the auto-tactic pre-pass
# exact? searches all of Mathlib. A hit costs ~8s; this caps what a miss can waste,
# since a miss is pure overhead on top of the LLM retry that follows.
PREMISE_SEARCH_TIMEOUT = 30

# Auto-tactics tried before calling the LLM for proof generation.
# Ordered fastest-first: rfl (instant), omega (linear Nat/Int), norm_num (numeric),
# linarith/ring (rational and real arithmetic — the usual modelling of floats),
# decide (finite decidable), simp (last resort).
#
# Each alternative is followed by `done`: `first` commits to whichever branch
# succeeds, and norm_num and simp succeed by making progress without closing the
# goal, which would shadow every later alternative.
_AUTO_TACTIC_STEPS = ("rfl", "omega", "norm_num", "linarith", "ring", "decide", "simp")
AUTO_TACTICS = "first | " + " | ".join(f"({step}; done)" for step in _AUTO_TACTIC_STEPS)


# ── Lean environment cache ─────────────────────────────────────────────────────
# Running `lake env lean` on every verification call re-invokes `lake` just to
# set environment variables. We capture those variables once at first use and
# call `lean` directly afterwards, saving ~100 ms per call.

_lean_env: dict | None = None
_lean_env_tried: bool = False


def _get_lean_env() -> dict | None:
    """Return the lake-managed environment, or None on failure (caller falls back)."""
    global _lean_env, _lean_env_tried
    if _lean_env_tried:
        return _lean_env
    _lean_env_tried = True
    lake = toolchain.which("lake")
    if lake is None:
        return None
    try:
        result = subprocess.run(
            [lake, "env", "env"],
            capture_output=True,
            text=True,
            cwd=str(LEAN_PROJECT_DIR),
            env=toolchain.env(),
            timeout=30,
        )
        if result.returncode == 0:
            env = toolchain.env()
            for line in result.stdout.splitlines():
                if "=" in line:
                    k, _, v = line.partition("=")
                    env[k] = v
            _lean_env = env
    except Exception:
        pass  # fall back to lake env lean per-call
    return _lean_env


# ── Data types ─────────────────────────────────────────────────────────────────


@dataclass
class LeanResult:
    success: bool
    output: str
    errors: list[dict] = field(default_factory=list)

    @property
    def first_error(self) -> dict | None:
        return self.errors[0] if self.errors else None

    def hint_for_error(self) -> str:
        if not self.errors:
            return ""
        return hints.hint_for(self.errors[0].get("data", ""))


# ── Verification ───────────────────────────────────────────────────────────────


STALE_TEMP_AGE = 3600


def sweep_stale_temps(verify_dir: Path) -> None:
    """Remove scratch files stranded by a killed run; live ones are far younger."""
    cutoff = time.time() - STALE_TEMP_AGE
    for path in verify_dir.glob("tmp_*.lean"):
        try:
            if path.stat().st_mtime < cutoff:
                path.unlink(missing_ok=True)
        except OSError:
            pass


def verify(lean_code: str, timeout: int | None = None) -> LeanResult:
    """Write lean_code to a temp file and verify it with lean --json."""
    if not lean_code or not lean_code.strip():
        return LeanResult(success=False, output="Empty Lean code", errors=[])

    verify_dir = LEAN_PROJECT_DIR / "Verify"
    verify_dir.mkdir(parents=True, exist_ok=True)
    sweep_stale_temps(verify_dir)

    with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", dir=verify_dir, delete=False, prefix="tmp_") as f:
        f.write(lean_code)
        tmp_path = Path(f.name)

    effective_timeout = timeout if timeout is not None else LEAN_TIMEOUT
    lean_env = _get_lean_env()

    if lean_env is not None:
        cmd = [toolchain.which("lean") or "lean", "--json", str(tmp_path)]
        env = lean_env
    else:
        cmd = [toolchain.which("lake") or "lake", "env", "lean", "--json", str(tmp_path)]
        env = toolchain.env()

    try:
        result = subprocess.run(
            sandbox.wrap(cmd),
            capture_output=True,
            text=True,
            timeout=effective_timeout,
            cwd=str(LEAN_PROJECT_DIR),
            env=env,
        )

        errors: list[dict] = []
        all_output_lines: list[str] = []

        for line in result.stdout.splitlines():
            all_output_lines.append(line)
            try:
                msg = json.loads(line)
                if msg.get("severity") == "error":
                    # Ignore the "uses sorry" pseudo-error — it means proof incomplete
                    if "declaration uses 'sorry'" not in msg.get("data", ""):
                        errors.append(msg)
            except json.JSONDecodeError:
                pass

        # Also surface any sorry warnings as errors so retries trigger
        for line in result.stdout.splitlines():
            try:
                msg = json.loads(line)
                if msg.get("severity") == "warning" and "sorry" in msg.get("data", ""):
                    errors.append({**msg, "severity": "error"})
            except json.JSONDecodeError:
                pass

        combined_output = "\n".join(all_output_lines)
        if result.stderr:
            combined_output += "\n" + result.stderr

        success = result.returncode == 0 and not errors
        return LeanResult(success=success, output=combined_output, errors=errors)

    except subprocess.TimeoutExpired:
        return LeanResult(
            success=False,
            output=f"Lean verification timed out after {effective_timeout}s",
            errors=[{"severity": "error", "data": "timeout", "line": 0, "col": 0}],
        )
    finally:
        tmp_path.unlink(missing_ok=True)


def check_syntax(lean_code: str) -> tuple[bool, str]:
    """Fast pre-check before invoking the full Lean verifier."""
    if not lean_code or not lean_code.strip():
        return False, "Empty Lean code"
    required = {"import", "theorem", "lemma", "def", "example"}
    if not any(kw in lean_code for kw in required):
        return False, "Code must contain at least one of: import, theorem, lemma, def, example"
    return True, ""


def replace_proof(lean_code: str, tactic: str) -> str | None:
    """Swap a model-written proof for `tactic`, or None if that would mean guessing.

    Only a single proof is rewritten, and only when nothing follows it — anything
    else would require knowing where one declaration ends and the next begins.
    """
    if lean_code.count(":= by") != 1:
        return None
    head, _, tail = lean_code.partition(":= by")
    if re.search(r"^\s*(theorem|lemma|def|example|instance|abbrev)\b", tail, re.MULTILINE):
        return None
    return f"{head}:= by {tactic}\n"


def as_auto_tactic_attempt(lean_code: str) -> str | None:
    """Worth trying before an LLM retry: the chain closes rfl, arithmetic and simp goals."""
    return replace_proof(lean_code, AUTO_TACTICS)


def as_premise_search(lean_code: str) -> str | None:
    """`exact?` searches Mathlib for a term closing the goal, and names what it finds.

    Where the tactic chain guesses from a fixed list, this retrieves — which is the
    failure that dominates in practice: not a wrong tactic, but not knowing which
    lemma exists.
    """
    return replace_proof(lean_code, "exact?")


_SUGGESTION = re.compile(r"Try this:\s*(?:\[[^\]]*\]\s*)?(.+)")


def suggested_tactic(output: str) -> str | None:
    """Pull the tactic out of Lean's `Try this:` suggestion."""
    for line in output.splitlines():
        try:
            data = json.loads(line).get("data", "")
        except json.JSONDecodeError:
            data = line
        match = _SUGGESTION.search(data)
        if match:
            # rstrip takes a character set, not a suffix — stripping "\\n" that way
            # would eat a trailing n from `exact Nat.le_refl n`.
            tactic = match.group(1).splitlines()[0].strip().strip('"').strip()
            if tactic:
                return tactic
    return None


def with_auto_tactics(lean_code: str) -> str:
    """Replace sorry placeholders with fast auto-tactics for a quick proof attempt."""
    replaced = lean_code.replace(":= by sorry", f":= by {AUTO_TACTICS}")
    replaced = replaced.replace("by\n  sorry", f"by {AUTO_TACTICS}")
    return replaced


# ── Batched verification ───────────────────────────────────────────────────────


@dataclass
class BatchEntry:
    key: str
    lean_code: str
    first_line: int = 0
    last_line: int = 0
    # Where each body line came from in the submitted proof. Imports are hoisted out
    # of the batch, so the nth body line is rarely the nth line the caller wrote, and
    # a position it cannot locate in its own file is worse than none.
    source_lines: list[int] = field(default_factory=list)


def error_position(error: dict) -> tuple[int | None, int | None]:
    """Lean reports a position under `pos`; older shapes used flat keys."""
    pos = error.get("pos") or {}
    line = pos.get("line", error.get("line"))
    col = pos.get("column", error.get("col"))
    return line, col


def _split_imports(lean_code: str) -> tuple[list[str], list[str], list[int]]:
    """Split off the imports, remembering where each surviving line started."""
    imports, body, source_lines = [], [], []
    for number, line in enumerate(lean_code.splitlines(), start=1):
        if line.strip().startswith("import "):
            imports.append(line)
        else:
            body.append(line)
            source_lines.append(number)
    return imports, body, source_lines


def build_batch(entries: list[BatchEntry]) -> str:
    """Assemble one Lean file from several independent proofs.

    Imports are hoisted because Lean only accepts them at the top of a file, and
    each proof is namespaced so identically named definitions cannot collide.
    """
    seen_imports: list[str] = []
    blocks: list[str] = []
    for index, entry in enumerate(entries):
        imports, body, entry.source_lines = _split_imports(entry.lean_code)
        for line in imports:
            if line.strip() not in seen_imports:
                seen_imports.append(line.strip())
        blocks.append((f"Batch{index}", entry, body))

    lines = list(seen_imports)
    if not lines:
        lines = ["import Mathlib"]
    lines.append("")

    for namespace, entry, body in blocks:
        lines.append(f"namespace {namespace}")
        entry.first_line = len(lines) + 1
        lines.extend(body)
        entry.last_line = len(lines)
        lines.append(f"end {namespace}")
        lines.append("")
    return "\n".join(lines)


def verify_batch(entries: list[BatchEntry], timeout: int | None = None) -> dict[str, LeanResult] | None:
    """Check several proofs in a single Lean invocation, paying one Mathlib import.

    Returns per-key results, or None when the batch itself could not be run — the
    caller then falls back to verifying each proof on its own.
    """
    if not entries:
        return {}

    batch_source = build_batch(entries)
    result = verify(batch_source, timeout=timeout)

    # An error outside every namespace (a bad hoisted import, say) invalidates the
    # whole batch rather than any one proof.
    for error in result.errors:
        line = error_position(error)[0] or 0
        if not any(e.first_line <= line <= e.last_line for e in entries):
            return None
    if not result.success and not result.errors:
        return None

    per_key: dict[str, LeanResult] = {}
    for entry in entries:
        errors = [
            _rebase(e, entry)
            for e in result.errors
            if entry.first_line <= (error_position(e)[0] or 0) <= entry.last_line
        ]
        per_key[entry.key] = LeanResult(
            success=not errors,
            output=result.output if errors else "",
            errors=errors,
        )
    return per_key


def _rebase(error: dict, entry: BatchEntry) -> dict:
    """Move a position from the concatenated batch back into the submitted proof."""
    line = error_position(error)[0]
    if line is None:
        return error
    index = line - entry.first_line
    if not 0 <= index < len(entry.source_lines):
        return error
    rebased = {**error, "pos": {**(error.get("pos") or {}), "line": entry.source_lines[index]}}
    rebased.pop("line", None)
    return rebased
