import os
import time
from dataclasses import dataclass, field

from . import prompts, proof_cache
from .feature_extractor import Property, PureFunction
from .lean_verifier import (
    AUTO_TACTIC_TIMEOUT,
    LeanResult,
    as_auto_tactic_attempt,
    check_syntax,
    verify,
    with_auto_tactics,
)
from .llm_client import call_llm, extract_code_block
from .logger import get_logger, log

_log = get_logger(__name__)


def _fmt_elapsed(seconds: float) -> str:
    if seconds < 60:
        return f"{seconds:.1f}s"
    m, s = divmod(int(seconds), 60)
    return f"{m}m {s}s"


@dataclass
class PropertyResult:
    property_id: str
    description: str
    kind: str
    function: str
    verified: bool
    lean_code: str
    lean_output: str
    retries: int
    reason: str = ""
    status: str = "failed"  # "verified" | "failed" | "unverifiable" | "error"
    preconditions: list[str] = field(default_factory=list)
    assumptions: list[str] = field(default_factory=list)
    cached: bool = False


def error_result(prop: Property, reason: str) -> "PropertyResult":
    """A failure of this tool, not a verdict about the code under test."""
    return PropertyResult(
        property_id=prop.id,
        description=prop.description,
        kind=prop.kind,
        function=prop.function,
        verified=False,
        lean_code="",
        lean_output="",
        retries=0,
        reason=reason,
        status="error",
        preconditions=prop.preconditions,
        assumptions=prop.assumptions,
    )


def unverifiable_result(prop: Property, reason: str) -> "PropertyResult":
    return PropertyResult(
        property_id=prop.id,
        description=prop.description,
        kind=prop.kind,
        function=prop.function,
        verified=False,
        lean_code="",
        lean_output="",
        retries=0,
        reason=reason,
        status="unverifiable",
        preconditions=prop.preconditions,
        assumptions=prop.assumptions,
    )


@dataclass
class Formalization:
    """A property that has been turned into Lean and still needs proving."""

    prop: Property
    key: str
    proof_code: str
    started_at: float


def verify_property(
    prop: Property,
    pure_fn: PureFunction | None,
    max_retries: int = None,
    language: str = "Python",
) -> PropertyResult:
    """Autoformalize once, then retry proof generation on failure."""
    outcome = formalize(prop, pure_fn, language=language)
    if isinstance(outcome, PropertyResult):
        return outcome
    return prove(outcome, max_retries=max_retries)


def formalize(
    prop: Property,
    pure_fn: PureFunction | None,
    language: str = "Python",
) -> "PropertyResult | Formalization":
    """Turn a property into Lean, returning a finished result when no proof is needed."""
    _t0 = time.monotonic()
    function_code = pure_fn.code if pure_fn else ""

    # ── Cache lookup ──────────────────────────────────────────────────────────
    key = proof_cache.cache_key(
        function_code, prop.description, prop.kind, prop.formal, prop.preconditions, prop.assumptions
    )
    cached = proof_cache.load(key)
    if cached is not None:
        elapsed = _fmt_elapsed(time.monotonic() - _t0)
        log(_log, "CACHE", f"{prop.id} [{prop.kind}] cache hit — skipping proof ({elapsed})")
        cached.property_id = prop.id
        cached.cached = True
        return cached

    # ── Step 1: Formalize AND prove in one LLM call ───────────────────────────
    log(_log, "VERIFY", f"{prop.id} [{prop.kind}] Formalizing+proving: {prop.description}")
    raw = call_llm(
        prompts.AUTOFORMALIZE_SYSTEM,
        prompts.PROPERTY_FORMALIZE_AND_PROVE_USER.format(
            language=language,
            function_code=function_code,
            description=prop.description,
            formal=prop.formal,
            kind=prop.kind,
            preconditions="\n".join(f"- {p}" for p in prop.preconditions) or "none",
            assumptions="\n".join(f"- {a}" for a in prop.assumptions) or "none",
        ),
    )
    proof_code = extract_code_block(raw, "lean4") or extract_code_block(raw, "lean")

    log(_log, "LEAN", f"{prop.id} formalized:\n{proof_code}")
    ok, syntax_error = check_syntax(proof_code)
    if not ok:
        return PropertyResult(
            property_id=prop.id,
            description=prop.description,
            kind=prop.kind,
            function=prop.function,
            verified=False,
            lean_code=proof_code,
            lean_output=syntax_error,
            retries=0,
            reason=f"Syntax error in formalization: {syntax_error}",
            preconditions=prop.preconditions,
            assumptions=prop.assumptions,
        )

    # ── Step 2: Auto-tactic pre-pass (if LLM left any sorry) ─────────────────
    # Fast tactics (rfl, omega, norm_num, decide, simp) close ~30% of properties
    # without any further LLM call.
    if "sorry" in proof_code:
        auto_code = with_auto_tactics(proof_code)
        log(_log, "VERIFY", f"{prop.id} trying auto-tactics (timeout {AUTO_TACTIC_TIMEOUT}s)...")
        auto_result = verify(auto_code, timeout=AUTO_TACTIC_TIMEOUT)
        if auto_result.success:
            log(_log, "OK", f"{prop.id} ✓ auto-proved ({_fmt_elapsed(time.monotonic() - _t0)})")
            result = PropertyResult(
                property_id=prop.id,
                description=prop.description,
                kind=prop.kind,
                function=prop.function,
                verified=True,
                lean_code=auto_code,
                lean_output=auto_result.output,
                retries=0,
                status="verified",
                preconditions=prop.preconditions,
                assumptions=prop.assumptions,
            )
            proof_cache.save(key, result)
            return result

    return Formalization(prop=prop, key=key, proof_code=proof_code, started_at=_t0)


def prove(
    formalization: Formalization,
    first_result: LeanResult | None = None,
    max_retries: int = None,
) -> PropertyResult:
    """Check a formalized property, retrying with error-specific hints on failure.

    first_result lets a caller supply the outcome of a batched Lean run, so the
    opening attempt does not pay its own Mathlib import.
    """
    prop = formalization.prop
    key = formalization.key
    proof_code = formalization.proof_code
    _t0 = formalization.started_at
    max_retries = max_retries or int(os.getenv("MAX_PROOF_RETRIES", "3"))

    retries = 0
    prev_error: str | None = None

    lean_result = first_result if first_result is not None else verify(proof_code)
    if lean_result.success:
        log(_log, "OK", f"{prop.id} ✓ verified ({_fmt_elapsed(time.monotonic() - _t0)})")
    else:
        # One Lean run is far cheaper than an LLM round-trip, and the chain closes
        # rfl, arithmetic and simp goals outright.
        auto_code = as_auto_tactic_attempt(proof_code)
        if auto_code is not None:
            log(_log, "VERIFY", f"{prop.id} trying auto-tactics before an LLM retry...")
            auto_result = verify(auto_code, timeout=AUTO_TACTIC_TIMEOUT)
            if auto_result.success:
                proof_code, lean_result = auto_code, auto_result
                log(_log, "OK", f"{prop.id} ✓ auto-proved ({_fmt_elapsed(time.monotonic() - _t0)})")

    for attempt in range(max_retries - 1):  # one attempt already used above
        if lean_result and lean_result.success:
            break
        err = (lean_result.first_error or {}).get("data", "unknown") if lean_result else "no result"
        log(_log, "FAIL", f"{prop.id} ✗ attempt {attempt + 1} failed: {err}")

        # If the error is identical to the previous attempt the LLM is stuck —
        # another retry with the same hint won't help, so bail out early.
        if err == prev_error:
            log(_log, "FAIL", f"{prop.id} ✗ same error twice — giving up early")
            break
        prev_error = err

        log(_log, "VERIFY", f"{prop.id} generating proof (attempt {attempt + 2}/{max_retries})...")

        err_dict = lean_result.first_error or {} if lean_result else {}
        proof_raw = call_llm(
            prompts.PROOF_GENERATION_SYSTEM,
            prompts.PROOF_RETRY_USER.format(
                error=err_dict.get("data", "unknown error"),
                line=err_dict.get("line", "?"),
                col=err_dict.get("col", "?"),
                hint=lean_result.hint_for_error() if lean_result else "",
                current=proof_code,
            ),
        )
        retries += 1
        proof_code = extract_code_block(proof_raw, "lean4") or extract_code_block(proof_raw, "lean") or proof_code
        log(_log, "LEAN", f"{prop.id} proof:\n{proof_code}")
        lean_result = verify(proof_code)
        if lean_result.success:
            log(_log, "OK", f"{prop.id} ✓ verified ({_fmt_elapsed(time.monotonic() - _t0)})")
            break
        else:
            err = (lean_result.first_error or {}).get("data", "unknown")
            log(_log, "FAIL", f"{prop.id} ✗ attempt {attempt + 2} failed: {err}")

    verified = lean_result.success if lean_result else False
    output = lean_result.output if lean_result else "No result"
    elapsed = _fmt_elapsed(time.monotonic() - _t0)
    if not verified:
        log(_log, "FAIL", f"{prop.id} ✗ exhausted {max_retries} attempts ({elapsed})")

    result = PropertyResult(
        property_id=prop.id,
        description=prop.description,
        kind=prop.kind,
        function=prop.function,
        verified=verified,
        lean_code=proof_code,
        lean_output=output,
        retries=retries,
        status="verified" if verified else "failed",
        preconditions=prop.preconditions,
        assumptions=prop.assumptions,
    )
    if verified:
        proof_cache.save(key, result)
    return result


def _fake_error(msg: str) -> LeanResult:
    from .lean_verifier import LeanResult

    return LeanResult(
        success=False,
        output=msg,
        errors=[{"severity": "error", "data": msg, "line": 0, "col": 0}],
    )
