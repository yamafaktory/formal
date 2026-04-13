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
        if "unsolved goals" in data and ".length" in data and '< "' in data:
            return (
                'Each case has a remaining goal of the form `0 < "literal".length` — '
                "these are closed concrete propositions (no free variables), so use `decide` "
                "or `norm_num` to close them. "
                "Add `· decide` (or `· norm_num`) after each case branch, "
                "or add `all_goals decide` at the end to close all such goals at once. "
                "Do NOT use `omega` — it cannot evaluate un-reduced string literal lengths."
            )
        if "unsolved goals" in data and "isPrefixOf" in data and "++" in data:
            return (
                "The goal `p.isPrefixOf (p ++ rest) = true` was not closed by simp. "
                "Try these strategies in order until one compiles:\n"
                "(1) Direct lemma (if it exists):\n"
                "  exact String.isPrefixOf_append_left _ _\n"
                "(2) Existence-witness form (most portable — does not depend on a specific lemma name):\n"
                "  rw [show (p ++ rest).isPrefixOf = _ from rfl]  -- skip if already in final form\n"
                "  simp only [String.isPrefixOf_iff]\n"
                "  exact ⟨rest, by simp [String.append_assoc]⟩\n"
                "(3) List-level fallback:\n"
                "  simp only [String.isPrefixOf, String.toList_append]\n"
                "  exact List.isPrefixOf_append_left _ _\n"
                "Do NOT use `decide` — free variables make the goal non-ground."
            )
        if "No goals" in data or "no goals" in data:
            if "cases" in data or "Cases" in data:
                return (
                    "One of the `cases` (or `match`) branches already closed its goal before all its "
                    "tactics ran. Each branch must be proved independently — remove any tactics that "
                    "appear after the goal is already closed in that branch."
                )
            return (
                "A tactic ran but there were no goals left — an earlier tactic already closed everything. "
                "Common causes:\n"
                "(1) A tactic like `simp at h`, `exact`, or `rw` closed the goal and you have extra "
                "tactics after it. Remove them.\n"
                "(2) In an `iff` proof with `constructor` + `split_ifs at h`, if `simp at h` in one "
                "branch fails to close by contradiction (e.g. `h : Except.ok X = Except.error ()`), "
                "that sub-goal leaks out and the backward-direction `·` bullet ends up on the wrong goal. "
                "Fix: replace bare `simp at h` with `exact absurd h (by simp)` or `simp [Except.ok.injEq] at h` "
                "to guarantee the contradiction closes the branch.\n"
                "(3) For the backward direction of `iff` with `if-then-else`: prefer\n"
                "    `simp only [functionName, if_pos h]`\n"
                "  over `unfold` + `rw [if_pos h]` — the `rw` closes the goal automatically "
                "via rfl, leaving nothing for subsequent tactics."
            )
        if "split_ifs" in data and "no if-then-else" in data:
            return (
                "`split_ifs` requires a visible `if`-`then`-`else` — there is none here. "
                "Do NOT call `split_ifs`. Instead: "
                "(1) use `obtain ⟨h1, h2⟩ := h` to split a conjunction hypothesis, "
                "(2) then case on the list to reduce it to a singleton "
                "(`cases l with | nil => simp at h1 | cons a t => cases t with | nil => ... | cons b t => omega`), "
                "(3) then `simp` to close the membership goal."
            )
        if "constructor" in data and "no applicable constructor" in data:
            # Check if it looks like an arithmetic goal in a list-induction cons case
            if "zipWith" in data or "sum" in data or ("*" in data and "=" in data):
                return (
                    "The goal is an arithmetic equation — `constructor` does not apply here. "
                    "In a list-induction cons case with a 'all elements satisfy P' hypothesis, "
                    "the pattern is: (1) extract the head fact with "
                    "`have hhead := hweights _ (by simp)` (or `List.mem_cons_self`), "
                    "(2) build the tail hypothesis with "
                    "`have htail : ∀ x ∈ tl, P x := fun x hx => hweights x (by simp [hx])`, "
                    "(3) apply the IH to the tail, "
                    "(4) close with `simp [hhead, mul_zero, ih]` or `linarith`/`ring`."
                )
            return (
                "The goal is not a conjunction/disjunction — `constructor` does not apply. "
                "Use `exact h`, `assumption`, `linarith`, `ring`, or `omega` to close it directly."
            )
        if "simp made no progress" in data:
            return (
                "simp cannot simplify the target. Common causes and fixes: "
                "(1) Branch order after `split_ifs` depends on the guard shape: "
                "for `if !boolField then none else body`, the FIRST branch has `hGuard: !boolField = true` "
                "(meaning bool is FALSE, function returns none) — `simp at h` closes `h: none = some _` THERE, "
                "and the SECOND branch is the real-content branch. "
                "For a plain `if cond then body else none`, it is the opposite: first branch is real content. "
                "Check which branch you are in and move `simp at h` accordingly. "
                "(2) For list length contradictions: `simp [List.length_cons] at h` then `omega`. "
                "(3) `unfold f at h` or `delta f at h` to expand a definition simp cannot see through. "
                "(4) If `simp` makes no progress after `generalize`, the hypothesis still contains an unsimplified "
                "`if`-expression — use `split_ifs at h` BEFORE `generalize` to eliminate the guard first."
            )
        if any(k in data for k in ("unknown identifier", "unknown tactic", "Unknown constant", "unknown constant")):
            import re as _re

            # Check for specific commonly-guessed wrong lemma names and give the correct replacement
            wrong_name = _re.search(r"[Uu]nknown (?:identifier|constant) [`']([A-Za-z_.][A-Za-z0-9_.']*)[`']", data)
            if wrong_name:
                name = wrong_name.group(1)
                _KNOWN_RENAMES = {
                    "Nat.eq_comm": "`eq_comm` (works for any type, no `Nat.` prefix needed)",
                    "Int.eq_comm": "`eq_comm` (works for any type, no `Int.` prefix needed)",
                    "Nat.pow_add": "`pow_add : a ^ (m + n) = a ^ m * a ^ n` (no `Nat.` prefix needed)",
                    "Nat.pow_mul": "`pow_mul : a ^ (m * n) = (a ^ m) ^ n` (no `Nat.` prefix needed)",
                    "pow_le_pow_right": (
                        "`Nat.pow_le_pow_right (h : 0 < base) : n ≤ m → base^n ≤ base^m` for Nat, "
                        "or `pow_le_pow_right (h : 1 ≤ base) : n ≤ m → base^n ≤ base^m` for ordered semirings"
                    ),
                    "pow_le_pow_left": ("`pow_le_pow_left (h : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a^n ≤ b^n`"),
                    "List.length_eq_one": (
                        "Lean 4 Mathlib does not have `List.length_eq_one`. "
                        "Case on the list: `cases l with | nil => simp | cons a t => cases t with "
                        "| nil => ... | cons b t => simp [List.length_cons] at h`"
                    ),
                }
                if name in _KNOWN_RENAMES:
                    return f"`{name}` does not exist. Use {_KNOWN_RENAMES[name]}."

            # Distinguish missing local hypotheses (e.g. h2, hne) from missing Mathlib names
            local_hyp = _re.search(r"[Uu]nknown identifier [`']([a-z_][a-zA-Z0-9_']*)[`']", data)
            if local_hyp and "." not in local_hyp.group(1):
                return (
                    f"`{local_hyp.group(1)}` is not in the local context — it was never introduced. "
                    "`split_ifs with h1 h2` only names as many hypotheses as there are if-conditions split "
                    "in that goal; some branches may have fewer. "
                    "Use `simp [hypothesis]` to discharge conditions directly, or check the goal state "
                    "to see which names were actually introduced."
                )
            return (
                "That identifier or constant does not exist in Mathlib. Do not guess lemma names. "
                "Instead prove the goal with `simp`, `omega`, `decide`, `rfl`, or by unfolding "
                "the definition and casing on the structure."
            )
        if "application type mismatch" in data:
            if "Option" in data and "has type" in data and "expected to have type" in data:
                # Both sides are Option but with different inner types — field extraction needed
                import re as _re

                has_type = _re.search(r"has type\s+Option (\S+)", data)
                exp_type = _re.search(r"expected to have type\s+Option (\S+)", data)
                if has_type and exp_type and has_type.group(1) != exp_type.group(1):
                    return (
                        f"You have `Option {has_type.group(1)}` but `Option {exp_type.group(1)}` is needed. "
                        "Extract the field from inside the Option with `.map`: "
                        "e.g. `list.head?.map (·.id)` instead of `list.head?`."
                    )
            if "isSome" in data and "Option" in data:
                return (
                    "`Option.get` requires an explicit proof argument `h : o.isSome = true` — "
                    "it is NOT the same as `Option.get!`. "
                    "Use pattern matching instead: `rcases o with _ | v` "
                    "or `match o with | some v => ... | none => ...`"
                )
            if "sort 'Type" in data and "sort 'Prop'" in data:
                return (
                    "You passed a value where a proof is expected. "
                    "The lemma takes a *proof* (e.g. `h : l ≠ []`) not the value itself (e.g. `l`). "
                    "Pass the proof term, or derive it with `by simp`, `by omega`, or from a hypothesis."
                )
            if ".data" in data:
                return (
                    "A list lemma was applied to a struct's `.data` field, but the lemma operates on "
                    "`List` directly — the struct's `++` is not the same as `List.append`. "
                    "Fix: (1) Add `have happ : (s ++ t).data = s.data ++ t.data := rfl` (or `by simp`) "
                    "and `rw [happ]` before applying the lemma, or "
                    "(2) redesign the model to use `List T` directly instead of a struct with a `.data` field — "
                    "this is almost always cleaner: just type-alias the aggregation as `List T`."
                )
            # IH used as a value when it is still a function waiting for its hypothesis argument
            if "has type" in data and "→" in data and "but is expected to have type" in data:
                import re as _re

                # Extract the IH name if present
                ih_name_match = _re.search(r"The argument\s+(\w+)\s+has type", data)
                ih_name = ih_name_match.group(1) if ih_name_match else "ih"
                # Extract the required hypothesis type (left side of the arrow in the IH type)
                arrow_match = _re.search(r"has type\s+(.+?)\s+→", data)
                required = arrow_match.group(1).strip() if arrow_match else "the required hypothesis"
                return (
                    f"`{ih_name}` is a function — it still needs its hypothesis argument before it becomes a proof. "
                    f"You must apply it: `{ih_name} (proof_of_{required.replace(' ', '_')})` where the argument "
                    f"proves `{required}`. "
                    f"Common proofs for arithmetic preconditions: `Nat.le_add_right n k` (proves `n ≤ n + k`), "
                    f"`Nat.le_refl n` (proves `n ≤ n`), or `by omega`. "
                    f"Do NOT pass `{ih_name}` to `le_trans` or other lemmas without applying it first."
                )
            return (
                "The argument has the wrong type. Common causes: "
                "(1) An induction hypothesis is still a function (has `→` in its type) — you must apply it "
                "to a proof of its precondition before using it as a value. "
                "(2) Passing a struct where a field value is needed — access it explicitly (e.g. `.id`). "
                "Read the expected type in the error and find or derive a proof of exactly that type."
            )
        if "type mismatch" in data:
            if "expected to have type" in data and "true = true" in data:
                return (
                    "The goal has already been reduced to `true = true` (the field was unfolded to `true`), "
                    "but you passed a hypothesis `h : x.field = true` where `true = true` is expected. "
                    "Don't use `exact h` here — close the goal with `rfl` instead. "
                    "If the goal still contains the field name, use `simp [h]` to rewrite it first."
                )
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
        if "Expected type must not contain free variables" in data:
            return (
                "`decide` cannot work when the goal contains free variables. "
                "Do NOT use `decide`, and do NOT use `simp [String.startsWith, String.isPrefixOf]` — "
                "that also fails to close goals with free-variable strings. "
                "For `p.isPrefixOf (p ++ rest) = true` or `(p ++ rest).startsWith p` goals:\n"
                "  exact String.isPrefixOf_append_left _ _\n"
                "  -- or: simp only [String.isPrefixOf, String.toList_append]; exact List.isPrefixOf_append_left _ _\n"
                "For the suffix-witness form `String.startsWith_iff_isPrefixOf`:\n"
                "  simp only [String.startsWith_iff_isPrefixOf]\n"
                "  exact ⟨rest, by simp [String.append_assoc]⟩\n"
                "For non-string goals with free variables: use `simp`, `omega`, `ring`, or `linarith`."
            )
        if "omega could not prove" in data and ".length" in data:
            return (
                '`omega` cannot evaluate string or list literal lengths (e.g. `"WEIGHTED_SUM((".length`) — '
                "they are not automatically reduced to numbers. "
                "Fix: run `simp only [String.length_mk, List.length]` or `norm_num` first to reduce all "
                "literal `.length` calls to concrete numbers, then `omega` for the remaining arithmetic. "
                "Alternatively, use `simp [String.length, String.append_length]` to normalise the whole goal."
            )
        if "declaration uses 'sorry'" in data:
            return "Replace sorry with a real proof. Try omega, simp, decide, or rfl."
        if data == "timeout":
            return (
                "The proof timed out. Try a faster strategy:\n"
                "(1) Replace `simp` chains with `omega` (Nat/Int arithmetic) or `linarith`/`ring` (Rat/Real).\n"
                "(2) For commutativity/linearity over Rat: `ring` closes most goals directly.\n"
                "(3) For a property about a specific enum/constructor value (e.g. `h : op = PLUS`): "
                "use `subst h` to replace the variable with the concrete value everywhere, "
                "then `simp [PLUS.getPrecedence, PLUS.print, ...]` to reduce the multi-branch if/match. "
                "Do NOT use `decide` or `aesop` on open inductive types — they do not terminate.\n"
                "(4) For string injectivity (f a b = f a' b' → a = a' ∧ b = b'): "
                "use `String.mk.injEq` to reduce to `List Char` equality, then `simp [List.append_inj_iff]`.\n"
                "(5) Avoid `aesop` and `decide` on non-finite or large types — they do not terminate.\n"
                "(6) If the goal needs induction, make the induction hypothesis strong enough (generalize first)."
            )
        if "function expected" in data or "Function expected" in data:
            if "∃" in data or "Exists" in data:
                return (
                    "The term already has an existential type — you cannot apply it as a function. "
                    "To extract the witnesses, use `obtain ⟨a, b, h⟩ := term` instead of `term arg`."
                )
            if "mem_cons_self" in data:
                return (
                    "`List.mem_cons_self` takes ZERO explicit arguments — all its parameters are implicit. "
                    "Writing `List.mem_cons_self w` or `List.mem_cons_self _ _` is WRONG and will always fail. "
                    "Correct forms:\n"
                    "  · To close a goal `a ∈ a :: l`:  `exact List.mem_cons_self`  (nothing after it)\n"
                    "  · To pass as proof to another lemma, e.g. `hweights _ proof`:  "
                    "use `hweights _ (List.mem_cons_self)` — NO args after `mem_cons_self`, "
                    "or use an anonymous proof: `hweights _ (by simp)`."
                )
            if ".id" in data or "field" in data.lower():
                return (
                    "Lean parsed a space before `.field` as function application. "
                    "Write field access without a space: `x.id` not `x .id`. "
                    "Also avoid `head!` — use `List.head?` or case on the list instead."
                )
            # Detect Mathlib lemma (has type `... = ...`) being applied as a function
            if "has type" in data and ("= " in data or "↔" in data):
                import re as _re

                lemma_name = _re.search(r"Function expected at\s+(\S+)", data)
                name = lemma_name.group(1) if lemma_name else "that lemma"
                return (
                    f"`{name}` is a theorem/proposition, not a function — you cannot apply it to arguments. "
                    f"Use `simp [{name}]` or `rw [{name}]` to rewrite with it instead of passing arguments directly."
                )
            return (
                "You applied too many arguments — the term is already a value or proposition, not a function. "
                "Remove the extra argument(s) and use `exact` to close the goal directly."
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
