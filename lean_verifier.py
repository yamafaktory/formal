import json
import os
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

LEAN_PROJECT_DIR = Path(os.getenv("LEAN_PROJECT_DIR", "/lean_project"))
LEAN_TIMEOUT = int(os.getenv("LEAN_TIMEOUT", "120"))
AUTO_TACTIC_TIMEOUT = 20  # seconds for the auto-tactic pre-pass

# Auto-tactics tried before calling the LLM for proof generation.
# Ordered fastest-first: rfl (instant), omega (linear arith), norm_num
# (numeric), decide (finite decidable), simp (last resort).
AUTO_TACTICS = "first | rfl | omega | norm_num | decide | simp"

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
    try:
        result = subprocess.run(
            ["lake", "env", "env"],
            capture_output=True,
            text=True,
            cwd=str(LEAN_PROJECT_DIR),
            timeout=30,
        )
        if result.returncode == 0:
            env = dict(os.environ)
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
        data = self.errors[0].get("data", "")
        if "No goals" in data or "no goals" in data:
            if "cases" in data or "Cases" in data:
                return (
                    "One of the `cases` (or `match`) branches already closed its goal before all its "
                    "tactics ran. Each branch must be proved independently — remove any tactics that "
                    "appear after the goal is already closed in that branch."
                )
            return (
                "simp (or a previous tactic) already closed the goal. "
                "Remove every tactic that comes after it — there is nothing left to prove."
            )
        if "constructor" in data and "no applicable constructor" in data:
            return (
                "The goal is not a conjunction/disjunction — `constructor` does not apply. "
                "Use `exact h`, `assumption`, `linarith`, or `omega` to close it directly."
            )
        if "simp made no progress" in data:
            return (
                "simp cannot simplify the target. Try these alternatives: "
                "`omega` for length/arithmetic goals; "
                "`simp only [List.length_nil, List.length_cons]` for list length; "
                "`norm_num` for numeric equalities; "
                "`contradiction` or `exact absurd h (by simp)` if the hypothesis is contradictory; "
                "or `unfold f at h` to manually expand a definition before simplifying."
            )
        if any(k in data for k in ("unknown identifier", "unknown tactic", "Unknown constant", "unknown constant")):
            return (
                "That identifier or constant does not exist in Mathlib. Do not guess lemma names. "
                "Instead prove the goal with `simp`, `omega`, `decide`, `rfl`, or by unfolding "
                "the definition and casing on the structure."
            )
        if "type mismatch" in data:
            if "Bool" in data and ("= false" in data or "= true" in data):
                return (
                    "Bool equality goals like `x = true` and `¬(x = false)` are not automatically interchangeable. "
                    "Use `decide`, `simp [Bool.eq_true_iff_ne_false]`, or `cases x <;> simp` to normalise."
                )
            return "The types don't match. Check your annotations and coercions."
        if "failed to generate" in data and "Inhabited" in data:
            return (
                "The type has no default value so `Inhabited` cannot be derived — do NOT add `deriving Inhabited`. "
                "Avoid `List.head!` and `l[0]!` entirely. Use `List.head?` (returns `Option`) "
                "or case on the list structure to extract the element safely."
            )
        if "failed to synthesize" in data:
            if "OfNat" in data and "Fin" in data:
                return (
                    "You are indexing a list with a numeric literal used as `Fin n` where `n` is a variable — "
                    "Lean cannot synthesize `OfNat (Fin n)` for a non-concrete bound. "
                    "Case on the list structure instead of using `List.get`."
                )
            if "Inhabited" in data:
                return (
                    "`List.head!` and `l[0]!` require an `Inhabited` instance which the domain type may not have. "
                    "Use `List.head?` (returns `Option`) or case on the list structure to extract the element safely."
                )
            return "A typeclass instance is missing. Check your imports."
        if "declaration uses 'sorry'" in data:
            return "Replace sorry with a real proof. Try omega, simp, decide, or rfl."
        if "function expected" in data or "Function expected" in data:
            if "mem_cons_self" in data:
                return (
                    "`List.mem_cons_self` takes only implicit arguments — do NOT pass `a` or `[]` explicitly. "
                    "Use `simp` to close membership goals, or write `exact List.mem_cons_self` with no arguments."
                )
            if ".id" in data or "field" in data.lower():
                return (
                    "Lean parsed a space before `.field` as function application. "
                    "Write field access without a space: `x.id` not `x .id`. "
                    "Also avoid `head!` — use `List.head?` or case on the list instead."
                )
            return (
                "You applied too many arguments — the term is already a value or proposition, not a function. "
                "Remove the extra argument(s) and use `exact` to close the goal directly."
            )
        if "application type mismatch" in data:
            if "isSome" in data and "Option" in data:
                return (
                    "`Option.get` requires an explicit proof argument `h : o.isSome = true` — "
                    "it is NOT the same as `Option.get!`. "
                    "Use pattern matching instead: `rcases o with _ | v` "
                    "or `match o with | some v => ... | none => ...`"
                )
            if "sort 'Type'" in data and "sort 'Prop'" in data:
                return (
                    "You passed a value where a proof is expected. "
                    "The lemma takes a *proof* (e.g. `h : l ≠ []`) not the value itself (e.g. `l`). "
                    "Pass the proof term, or derive it with `by simp`, `by omega`, or from a hypothesis."
                )
            return (
                "The argument has the wrong type. If you are passing a struct where a field value is expected "
                "(e.g. a `Share` where a `String` is needed), access the field explicitly (e.g. `.id`). "
                "Check what type the goal expects and adjust accordingly."
            )
        return "Review Lean 4 syntax and ensure all imports are present."


# ── Verification ───────────────────────────────────────────────────────────────


def verify(lean_code: str, timeout: int | None = None) -> LeanResult:
    """Write lean_code to a temp file and verify it with lean --json."""
    if not lean_code or not lean_code.strip():
        return LeanResult(success=False, output="Empty Lean code", errors=[])

    verify_dir = LEAN_PROJECT_DIR / "Verify"
    verify_dir.mkdir(parents=True, exist_ok=True)

    with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", dir=verify_dir, delete=False, prefix="tmp_") as f:
        f.write(lean_code)
        tmp_path = Path(f.name)

    effective_timeout = timeout if timeout is not None else LEAN_TIMEOUT
    lean_env = _get_lean_env()

    if lean_env is not None:
        cmd = ["lean", "--json", str(tmp_path)]
        env = lean_env
    else:
        cmd = ["lake", "env", "lean", "--json", str(tmp_path)]
        env = None

    try:
        result = subprocess.run(
            cmd,
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


def with_auto_tactics(lean_code: str) -> str:
    """Replace sorry placeholders with fast auto-tactics for a quick proof attempt."""
    replaced = lean_code.replace(":= by sorry", f":= by {AUTO_TACTICS}")
    replaced = replaced.replace("by\n  sorry", f"by {AUTO_TACTICS}")
    return replaced
