import json
import os
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

LEAN_PROJECT_DIR = Path(os.getenv("LEAN_PROJECT_DIR", "/lean_project"))
LEAN_TIMEOUT = int(os.getenv("LEAN_TIMEOUT", "120"))


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
            return (
                "simp (or a previous tactic) already closed the goal. "
                "Remove every tactic that comes after it — there is nothing left to prove."
            )
        if "constructor" in data and "no applicable constructor" in data:
            return (
                "The goal is not a conjunction/disjunction — `constructor` does not apply. "
                "Use `exact h`, `assumption`, `linarith`, or `omega` to close it directly."
            )
        if "unknown identifier" in data or "unknown tactic" in data:
            return "Check that the identifier/tactic is in scope and spelled correctly."
        if "type mismatch" in data:
            return "The types don't match. Check your annotations and coercions."
        if "failed to synthesize" in data:
            return "A typeclass instance is missing. Check your imports."
        if "declaration uses 'sorry'" in data:
            return "Replace sorry with a real proof. Try omega, simp, decide, or rfl."
        if "application type mismatch" in data:
            return "Wrong number or type of arguments. Check the function signature."
        return "Review Lean 4 syntax and ensure all imports are present."


def verify(lean_code: str) -> LeanResult:
    """Write lean_code to a temp file and verify it with `lake env lean --json`."""
    if not lean_code or not lean_code.strip():
        return LeanResult(success=False, output="Empty Lean code", errors=[])

    verify_dir = LEAN_PROJECT_DIR / "Verify"
    verify_dir.mkdir(parents=True, exist_ok=True)

    with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", dir=verify_dir, delete=False, prefix="tmp_") as f:
        f.write(lean_code)
        tmp_path = Path(f.name)

    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--json", str(tmp_path)],
            capture_output=True,
            text=True,
            timeout=LEAN_TIMEOUT,
            cwd=str(LEAN_PROJECT_DIR),
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
            output=f"Lean verification timed out after {LEAN_TIMEOUT}s",
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
