import json
import os
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import sandbox, toolchain
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

# Verified against Lean v4.29.0 / Mathlib: every String-level route to a prefix
# goal fails, because String.startsWith now goes through the slice pattern API
# (String.Slice.Pattern.ForwardPattern) and String.isPrefixOf does not reduce.
# Converting to List Char with String.toList_append does work.
STRING_PREFIX_HINT = (
    "String-level prefix goals cannot be closed in this Lean version: `String.startsWith` is "
    "implemented through `String.Slice.Pattern.ForwardPattern`, and `String.isPrefixOf` does not "
    "reduce either — `simp`, `rfl`, `decide` and unfolding all fail on them.\n"
    "Convert to `List Char`, where the goal is trivial:\n"
    "  simp [String.toList_append, List.isPrefixOf]\n"
    "This closes goals of the form `a.toList.isPrefixOf (a ++ b).toList = true`.\n"
    "Better still, state the property over `List Char` in the first place — model the function as "
    "taking `List Char` rather than `String`, and `simp [List.isPrefixOf]`, `List.prefix_append` "
    "and `List.take_append` all apply directly.\n"
    "Use `.toList`, NOT `.data` — `.data` does not reduce. Do NOT use `String.isPrefixOf_iff`, "
    "`String.isPrefixOf_append_left` or `List.isPrefixOf_append_left`: they do not exist. "
    "`String.toList_append` takes no explicit arguments, so pass it to `simp`, never `exact`."
)


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
        if "not definitionally equal" in data and ("isPrefixOf" in data or "startsWith" in data):
            return STRING_PREFIX_HINT
        if "unsolved goals" in data and ("isPrefixOf" in data or "startsWith" in data) and "++" in data:
            return STRING_PREFIX_HINT
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
        if "invalid binder annotation" in data and "not a class instance" in data:
            return (
                "Square brackets `[h : T]` are reserved for typeclass arguments only — Lean rejected "
                "this because `T` is not a typeclass. "
                "Change every `[h : T]` in the theorem signature to `(h : T)` (round brackets). "
                "Example: `[h : op = PLUS]` → `(h : op = PLUS)`."
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
                        "For Nat: `Nat.pow_le_pow_right (h : 0 < base) (hle : n ≤ m) : base^n ≤ base^m`. "
                        "For general ordered semirings the bare `pow_le_pow_right` may not exist in this "
                        "Mathlib version. Use the `gcongr` tactic instead — it handles power monotonicity "
                        "goals automatically without needing the exact lemma name:\n"
                        "  gcongr  -- closes `x^n ≤ x^m` when `n ≤ m` and `1 ≤ x` are in context\n"
                        "Or decompose manually: `apply pow_le_pow_of_le_one` / `apply pow_le_one` "
                        "for base ≤ 1 cases."
                    ),
                    "pow_le_pow_left": ("`pow_le_pow_left (h : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a^n ≤ b^n`"),
                    "List.length_eq_one": (
                        "Lean 4 Mathlib does not have `List.length_eq_one`. "
                        "Case on the list: `cases l with | nil => simp | cons a t => cases t with "
                        "| nil => ... | cons b t => simp [List.length_cons] at h`"
                    ),
                    "List.append_right_cancel": (
                        "`List.append_right_cancel` does not exist in Mathlib. "
                        "To strip a common suffix `s` from `a ++ s = b ++ s`, use:\n"
                        "  have hlen : a.length = b.length := by\n"
                        "    have := congr_arg List.length h; simp [List.length_append] at this; omega\n"
                        "  exact (List.append_inj h hlen).1\n"
                        "`List.append_inj h hlen` requires the two PREFIX lengths to be equal, "
                        "then gives `prefix_l = prefix_r ∧ suffix_l = suffix_r`."
                    ),
                    "String.length_mk": (
                        "`String.length_mk` does not exist in Mathlib. "
                        "String literal lengths are definitionally equal to their character count — "
                        'use `show "literal".length = N from rfl` inline in a `simp only` call:\n'
                        "  simp only [String.length_append,\n"
                        '    show "PREFIX".length = N from rfl,\n'
                        '    show "SUFFIX".length = K from rfl]\n'
                        "  omega\n"
                        "Do NOT use `simp [String.length]` — it unfolds recursively and loops."
                    ),
                    "List.isPrefixOf_append_left": (
                        "`List.isPrefixOf_append_left` does not exist in Mathlib. "
                        "To prove `p.isPrefixOf (p ++ rest) = true`, unfold to `List.isPrefixOf` "
                        "and let simp reduce character-by-character:\n"
                        "  simp only [String.isPrefixOf, String.toList_append]  -- if still at String level\n"
                        "  simp [List.isPrefixOf]\n"
                        "This works even with free-variable suffixes because simp steps through "
                        "each concrete character in the prefix and closes after the last one."
                    ),
                    "List.append_left_cancel": (
                        "`List.append_left_cancel` does not exist in Mathlib. "
                        "To strip a common prefix `p` from `p ++ a = p ++ b`, use:\n"
                        "  exact (List.append_inj h rfl).2\n"
                        "`List.append_inj h rfl` works when the two prefixes are definitionally equal "
                        "(same literal), giving `prefix_l = prefix_r ∧ a = b`; take `.2` for the suffix."
                    ),
                    "Operator.decEq": (
                        "`Operator.decEq` does not exist as a standalone def. "
                        "DecidableEq is a typeclass instance, not a named lemma. "
                        "Fix options:\n"
                        "(1) Add `deriving DecidableEq` to the `Operator` inductive definition.\n"
                        "(2) Use `decide` directly on closed decidable goals.\n"
                        "(3) Use `instDecidableEqOperator` if the instance was auto-generated, "
                        "or just write the `DecidableEq Operator` instance manually."
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
                    f"`{ih_name}` is a function (type: `{required} → ...`) — you must apply it to a "
                    f"proof of `{required}` before passing it anywhere.\n"
                    f"WRONG:  `le_trans {ih_name} ...`  ← {ih_name} is not yet a proof, it's still a function\n"
                    f"RIGHT:  `le_trans ({ih_name} (by omega)) ...`  ← apply {ih_name} first\n"
                    f"Common proofs for arithmetic preconditions:\n"
                    f"  `by omega`                    — works for any linear arithmetic goal\n"
                    f"  `Nat.le_add_right n k`        — proves `n ≤ n + k`\n"
                    f"  `Nat.le_refl n`               — proves `n ≤ n`\n"
                    f"If the induction is over a difference `k` obtained via `obtain ⟨k, rfl⟩`, "
                    f"also consider replacing the whole induction with `gcongr` — for monotonicity "
                    f"goals like `a ^ m ≤ a ^ n` with `ha : 1 ≤ a` and `hmn : m ≤ n` in context, "
                    f"`gcongr` closes the goal in one step without any induction."
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
            if "isPrefixOf" in data or "startsWith" in data or "String" in data:
                return STRING_PREFIX_HINT
            return (
                "`decide` cannot work when the goal contains free variables. "
                "Use `simp`, `omega`, `ring`, or `linarith` instead, or case-split on the "
                "free variables until the remaining goals are ground."
            )
        if "omega could not prove" in data and ".length" in data:
            return (
                '`omega` cannot evaluate string literal lengths (e.g. `"WEIGHTED_SUM((".length`) — '
                "they appear as opaque variables to omega. "
                "String literal lengths are definitionally equal to their character count and can be "
                "reduced inline with `show ... from rfl`. Use this exact pattern:\n"
                "  simp only [String.length_append,\n"
                '    show "PREFIX".length = N from rfl,\n'
                '    show "MID".length = M from rfl,\n'
                '    show "SUFFIX".length = K from rfl]\n'
                "  omega\n"
                "Replace each literal and its count (N, M, K) with the actual strings and their "
                "character counts. Count carefully — every character including spaces and punctuation.\n"
                "IMPORTANT: do NOT use `simp [String.length]` or `simp [String.length_append, "
                "String.length]` — `String.length` unfolds recursively and causes maximum recursion depth errors.\n"
                "Also do NOT use `String.length_mk` — it does not exist in Mathlib."
            )
        if "ForwardPattern" in data or "Slice.Pattern" in data:
            return STRING_PREFIX_HINT
        if "has already been declared" in data:
            return (
                "The generated code redeclares a name that Mathlib already defines "
                "(commonly `Path`, `Option`, `Prod`, `List`, `String`, `Nat`, or a tactic name). "
                "`import Mathlib` brings it into scope, so the definition collides.\n"
                "Rename the local model with a prefix that cannot clash — `MyPath`, `SrcOption`, "
                "`ModelString` — and update every reference to it in the theorem and proof. "
                "Do NOT try to work around it with `namespace`, `open`, or `_root_.`: the theorem "
                "should model your function's own type, not shadow a Mathlib one."
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


def _split_imports(lean_code: str) -> tuple[list[str], list[str]]:
    imports, body = [], []
    for line in lean_code.splitlines():
        (imports if line.strip().startswith("import ") else body).append(line)
    return imports, body


def build_batch(entries: list[BatchEntry]) -> str:
    """Assemble one Lean file from several independent proofs.

    Imports are hoisted because Lean only accepts them at the top of a file, and
    each proof is namespaced so identically named definitions cannot collide.
    """
    seen_imports: list[str] = []
    blocks: list[str] = []
    for index, entry in enumerate(entries):
        imports, body = _split_imports(entry.lean_code)
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
        line = error.get("pos", {}).get("line") or error.get("line") or 0
        if not any(e.first_line <= line <= e.last_line for e in entries):
            return None
    if not result.success and not result.errors:
        return None

    per_key: dict[str, LeanResult] = {}
    for entry in entries:
        errors = [
            e
            for e in result.errors
            if entry.first_line <= (e.get("pos", {}).get("line") or e.get("line") or 0) <= entry.last_line
        ]
        per_key[entry.key] = LeanResult(
            success=not errors,
            output=result.output if errors else "",
            errors=errors,
        )
    return per_key
