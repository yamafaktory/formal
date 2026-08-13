"""Check caller-supplied Lean proofs. No LLM is involved.

This is the half of the pipeline that never needed a model: syntax screening, one
batched Lean run, and the recovery chain. An agent that writes its own Lean drives
this directly, and the LLM pipeline calls the same code after formalizing.
"""

import time
from dataclasses import dataclass

from .lean_verifier import (
    AUTO_TACTIC_TIMEOUT,
    LEAN_TIMEOUT,
    PREMISE_SEARCH_TIMEOUT,
    BatchEntry,
    LeanResult,
    as_auto_tactic_attempt,
    as_premise_search,
    check_syntax,
    error_position,
    replace_proof,
    suggested_tactic,
    verify,
    verify_batch,
)
from .logger import get_logger, log

_log = get_logger(__name__)


@dataclass
class Submission:
    """One Lean theorem to check, identified by a caller-chosen id."""

    id: str
    lean_code: str


@dataclass
class Outcome:
    """The verdict on one submission.

    Carries the first error and its hint rather than the full Lean output: a
    Mathlib failure runs to thousands of tokens, and everything past the first
    error is noise to whoever has to write the next attempt.
    """

    id: str
    status: str  # "verified" | "failed"
    lean_code: str
    error: str = ""
    line: int | None = None
    col: int | None = None
    hint: str = ""
    checked: bool = False

    @property
    def verified(self) -> bool:
        return self.status == "verified"


def can_cache(outcome: Outcome) -> bool:
    """Whether a verdict has earned a place in the durable cache.

    The cache outlives the run and is shared with the LLM pipeline, so a wrong
    entry is served as truth indefinitely. A session verdict only has to be right
    now; this has to be evidenced. `checked` is set where a LeanResult is turned
    into an outcome and nowhere else, so a hand-built or stubbed outcome — the way
    a mocked verifier reaches this code — cannot satisfy it.
    """
    if not outcome.verified or not outcome.checked:
        return False
    if "sorry" in outcome.lean_code:
        return False
    return check_syntax(outcome.lean_code)[0]


def recover_without_llm(entry_id: str, proof_code: str, started_at: float) -> tuple[str, LeanResult] | None:
    """Try the tactic chain, then Mathlib premise search, before paying for a retry."""
    auto_code = as_auto_tactic_attempt(proof_code)
    if auto_code is not None:
        log(_log, "VERIFY", f"{entry_id} trying auto-tactics before an LLM retry...")
        auto_result = verify(auto_code, timeout=AUTO_TACTIC_TIMEOUT)
        if auto_result.success:
            log(_log, "OK", f"{entry_id} ✓ auto-proved ({fmt_elapsed(time.monotonic() - started_at)})")
            return auto_code, auto_result

    search_code = as_premise_search(proof_code)
    if search_code is None:
        return None

    log(_log, "VERIFY", f"{entry_id} searching Mathlib for a closing lemma...")
    search_result = verify(search_code, timeout=PREMISE_SEARCH_TIMEOUT)
    tactic = suggested_tactic(search_result.output)
    if tactic is None:
        return None

    # Store the concrete term rather than the search tactic: exact? is slow to
    # re-check and its answer can move with Mathlib.
    log(_log, "LEAN", f"{entry_id} Mathlib suggests: {tactic}")
    final_code = replace_proof(proof_code, tactic)
    if final_code is None:
        return None
    final_result = verify(final_code)
    if final_result.success:
        log(_log, "OK", f"{entry_id} ✓ proved by premise search ({fmt_elapsed(time.monotonic() - started_at)})")
        return final_code, final_result
    if search_result.success:
        return search_code, search_result
    return None


def fmt_elapsed(seconds: float) -> str:
    if seconds < 60:
        return f"{seconds:.1f}s"
    m, s = divmod(int(seconds), 60)
    return f"{m}m {s}s"


def _to_outcome(entry_id: str, lean_code: str, result: LeanResult) -> Outcome:
    if result.success:
        return Outcome(id=entry_id, status="verified", lean_code=lean_code, checked=True)

    err = result.first_error
    if err is None:
        # Lean exited without a diagnostic anyone can act on — a crash, a timeout, a
        # blown recursion limit. Returning "unknown error" and no hint left the caller
        # with nothing at all, so hand over whatever Lean did say.
        tail = "\n".join(result.output.strip().splitlines()[-12:])
        return Outcome(
            id=entry_id,
            status="failed",
            lean_code=lean_code,
            error=tail or "Lean produced no output and no diagnostics",
            hint=(
                "Lean failed without reporting a position, which usually means it crashed or hit a "
                "limit rather than rejecting the proof: a blown `maxRecDepth`, `maxHeartbeats`, or a "
                "tactic that diverged. Reduce what the tactic has to chew on — case-split by hand "
                "instead of `decide` over a large finite type, and prefer `simp only [...]` with named "
                "lemmas over bare `simp`. Raising the limit usually moves the failure rather than "
                "removing it."
            ),
            checked=True,
        )

    line, col = error_position(err)
    return Outcome(
        id=entry_id,
        status="failed",
        lean_code=lean_code,
        error=str(err.get("data", "unknown error")),
        line=line,
        col=col,
        hint=result.hint_for_error(),
        checked=True,
    )


def check_batch(submissions: list[Submission], timeout: int | None = None) -> list[Outcome]:
    """Check every submission, recovering the failures that need no model.

    Syntax is screened first so a malformed proof never costs a Mathlib import.
    Whatever survives is checked in a single Lean run; a batch that cannot be
    attributed falls back to one run per submission.
    """
    outcomes: dict[str, Outcome] = {}
    pending: list[Submission] = []

    for sub in submissions:
        ok, syntax_error = check_syntax(sub.lean_code)
        if ok:
            pending.append(sub)
        else:
            log(_log, "FAIL", f"{sub.id} ✗ syntax error: {syntax_error}")
            outcomes[sub.id] = Outcome(
                id=sub.id,
                status="failed",
                lean_code=sub.lean_code,
                error=syntax_error,
                hint="The proof was rejected before Lean ran — fix the syntax first.",
            )

    batched: dict[str, LeanResult] = {}
    if len(pending) > 1:
        log(_log, "LEAN", f"Checking {len(pending)} proofs in one Lean run...")
        attributed = verify_batch(
            [BatchEntry(key=sub.id, lean_code=sub.lean_code) for sub in pending],
            timeout=timeout or LEAN_TIMEOUT,
        )
        if attributed is None:
            log(_log, "LEAN", "Batch could not be attributed — verifying individually")
        else:
            batched = attributed

    for sub in pending:
        started_at = time.monotonic()
        lean_code = sub.lean_code
        result = batched.get(sub.id) or verify(lean_code, timeout=timeout)
        if not result.success:
            recovered = recover_without_llm(sub.id, lean_code, started_at)
            if recovered is not None:
                lean_code, result = recovered
        outcomes[sub.id] = _to_outcome(sub.id, lean_code, result)

    return [outcomes[sub.id] for sub in submissions]
