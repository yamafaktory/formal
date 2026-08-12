import os
import pathlib
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass

from . import fidelity as fidelity_check
from .feature_extractor import (
    Property,
    decompose,
    extract_properties,
)
from .lean_verifier import LEAN_TIMEOUT, BatchEntry, LeanResult, verify_batch
from .logger import get_logger, log
from .property_verifier import Formalization, PropertyResult, error_result, formalize, prove, unverifiable_result

_log = get_logger(__name__)


@dataclass
class FeaturePipelineResult:
    feature_file: str
    feature_summary: str
    pure_functions: list[str]
    impure_parts: list[str]
    properties_found: int
    properties_verified: int
    properties_unverifiable: int
    results: list[PropertyResult]

    @property
    def properties_diverging(self) -> int:
        return sum(1 for r in self.results if r.fidelity == "diverges")

    @property
    def properties_errored(self) -> int:
        return sum(1 for r in self.results if r.status == "error")

    @property
    def overall_score(self) -> str:
        errored = self.properties_errored
        verifiable_count = self.properties_found - self.properties_unverifiable - errored
        if errored and verifiable_count == 0:
            return "error"
        if verifiable_count == 0:
            return "no_pure_logic"
        pct = self.properties_verified / verifiable_count
        if pct == 1.0:
            # "full" must mean every property was checked — an errored one was not.
            return "partial" if errored else "full"
        if pct >= 0.5:
            return "partial"
        return "failed"

    def summary(self) -> str:
        rule = "─" * 41
        errored = self.properties_errored
        counts = (
            f"{self.properties_verified}/{self.properties_found} verified, {self.properties_unverifiable} unverifiable"
        )
        if errored:
            counts += f", {errored} errored"
        score = f"{self.overall_score}  ({counts})"
        lines = [
            rule,
            f"File:    {self.feature_file}",
            f"Summary: {self.feature_summary}",
            f"Score:   {score}",
            f"Pure functions: {', '.join(self.pure_functions) or 'none'}",
            f"Impure parts: {len(self.impure_parts)} side effects (not verifiable)",
            rule,
        ]
        for r in self.results:
            if r.status == "verified":
                icon = "✓"
            elif r.status == "unverifiable":
                icon = "~"
            elif r.status == "error":
                icon = "!"
            else:
                icon = "✗"
            cached_marker = " [cached]" if r.cached else ""
            lines.append(f"  {icon} [{r.kind}] {r.description}{cached_marker}")
            if r.preconditions:
                lines.append(f"      Preconditions: {', '.join(r.preconditions)}")
            if r.assumptions:
                lines.append(f"      Assumptions:   {', '.join(r.assumptions)}")
            if r.status != "verified" and r.reason:
                lines.append(f"      → {r.reason}")
            if r.fidelity == "diverges":
                lines.append(f"      ⚠ theorem may not match this property: {r.fidelity_reason}")
                if r.back_translation:
                    lines.append(f"        Lean theorem states: {r.back_translation}")
        lines.append(rule)
        if self.properties_diverging:
            lines.append(
                f"{self.properties_diverging} verified propert(ies) may not say what was asked — "
                "read the theorem before relying on them."
            )
            lines.append(rule)
        if errored:
            lines.append(f"{errored} property/properties could not be checked — this is a tool failure, not a verdict.")
            lines.append(rule)
        return "\n".join(lines)


def run_feature_pipeline(
    code: str,
    feature_file: str = "<inline>",
    parallel: bool = True,
    language: str = "Python",
    check_fidelity: bool = False,
) -> FeaturePipelineResult:
    _t0 = time.monotonic()
    max_retries = int(os.getenv("MAX_PROOF_RETRIES", "3"))

    # ── Step 1: Decompose ────────────────────────────────────────────────────
    log(_log, "PIPELINE", f"Decomposing feature [{language}]: {feature_file}")
    feature = decompose(code, language=language)
    log(_log, "PIPELINE", f"Summary: {feature.feature_summary}")
    log(_log, "PIPELINE", f"Pure functions: {[f.name for f in feature.pure_functions] or 'none'}")
    log(_log, "PIPELINE", f"Impure parts: {len(feature.impure_parts)}")

    # Mark side-effect-only features early
    if not feature.pure_functions:
        log(_log, "PIPELINE", "No pure functions found — skipping verification")
        return FeaturePipelineResult(
            feature_file=feature_file,
            feature_summary=feature.feature_summary,
            pure_functions=[],
            impure_parts=feature.impure_parts,
            properties_found=0,
            properties_verified=0,
            properties_unverifiable=0,
            results=[],
        )

    # ── Step 2: Extract and screen properties ───────────────────────────────
    properties = extract_properties(feature, language=language)
    feature.properties = properties
    log(_log, "PIPELINE", f"Extracted {len(properties)} properties")

    verifiable = [p for p in properties if p.verifiable]
    unverifiable = [p for p in properties if not p.verifiable]

    for p in verifiable:
        log(_log, "SCREEN", f"✓ {p.id}: VERIFIABLE — {p.description}")
    for p in unverifiable:
        log(_log, "SCREEN", f"~ {p.id}: UNVERIFIABLE — {p.unverifiable_reason}")

    # Build results for unverifiable properties immediately
    unverifiable_results = [unverifiable_result(p, p.unverifiable_reason) for p in unverifiable]

    # ── Step 3: Verify each verifiable property (parallel or sequential) ─────
    fn_map = {f.name: f for f in feature.pure_functions}

    def _run(work, items):
        if not (parallel and len(items) > 1):
            return [work(item) for item in items]
        workers = min(len(items), int(os.getenv("MAX_PARALLEL_PROPERTIES", "4")))
        with ThreadPoolExecutor(max_workers=workers) as ex:
            futures = [ex.submit(work, item) for item in items]
            return [f.result() for f in futures]

    def _formalize_one(prop: Property) -> PropertyResult | Formalization:
        fn = fn_map.get(prop.function)

        # If the property references a named function that wasn't extracted, we have
        # no source code to re-implement in Lean — skip rather than sending an empty
        # prompt and burning 480s on a blind type-reconstruction attempt.
        if fn is None and prop.function and prop.function not in fn_map:
            reason = (
                f"Source function '{prop.function}' was not extracted as a pure function — "
                "cannot reconstruct its behavior for Lean verification."
            )
            log(_log, "SKIP", f"{prop.id} — {reason}")
            return unverifiable_result(prop, reason)

        try:
            return formalize(prop, fn, language=language)
        except Exception as e:
            log(_log, "ERROR", f"{prop.id} ✗ {type(e).__name__}: {e}")
            return error_result(prop, f"{type(e).__name__}: {e}")

    # ── Step 3a: Formalize every property (LLM-bound, so run these in parallel) ──
    formalized = _run(_formalize_one, verifiable)
    pending = [f for f in formalized if isinstance(f, Formalization)]
    verified_results = [r for r in formalized if isinstance(r, PropertyResult)]

    # ── Step 3b: Check every first attempt in one Lean run ──────────────────────
    # Each proof would otherwise pay its own `import Mathlib`, which dominates a
    # Lean invocation. A batch that cannot be attributed falls back to individual
    # verification inside prove().
    first_results: dict[str, LeanResult] = {}
    if len(pending) > 1:
        log(_log, "LEAN", f"Checking {len(pending)} first attempts in one Lean run...")
        batched = verify_batch(
            [BatchEntry(key=f.key, lean_code=f.proof_code) for f in pending],
            timeout=LEAN_TIMEOUT,
        )
        if batched is None:
            log(_log, "LEAN", "Batch could not be attributed — verifying individually")
        else:
            first_results = batched

    # ── Step 3c: Retry loop, per property and only where needed ─────────────────
    def _prove_one(f: Formalization) -> PropertyResult:
        try:
            return prove(f, first_result=first_results.get(f.key), max_retries=max_retries)
        except Exception as e:
            log(_log, "ERROR", f"{f.prop.id} ✗ {type(e).__name__}: {e}")
            return error_result(f.prop, f"{type(e).__name__}: {e}")

    verified_results += _run(_prove_one, pending)

    # Merge and sort back to original property order
    all_results = verified_results + unverifiable_results
    order = {p.id: i for i, p in enumerate(properties)}
    all_results.sort(key=lambda r: order.get(r.property_id, 999))

    # A verified property whose theorem says something else is the one failure that
    # looks like success, so the check only pays for itself on what Lean accepted.
    if check_fidelity:
        fidelity_check.annotate(all_results, _run)

    verified_count = sum(1 for r in all_results if r.status == "verified")
    unverifiable_count = sum(1 for r in all_results if r.status == "unverifiable")
    failed_count = sum(1 for r in all_results if r.status == "failed")
    errored_count = sum(1 for r in all_results if r.status == "error")
    elapsed = time.monotonic() - _t0
    m, s = divmod(int(elapsed), 60)
    elapsed_str = f"{m}m {s}s" if m else f"{s}s"
    log(
        _log,
        "PIPELINE",
        f"Done — verified: {verified_count}, failed: {failed_count}, unverifiable: {unverifiable_count}"
        + (f", errored: {errored_count}" if errored_count else "")
        + f" — total: {elapsed_str}",
    )

    return FeaturePipelineResult(
        feature_file=feature_file,
        feature_summary=feature.feature_summary,
        pure_functions=[f.name for f in feature.pure_functions],
        impure_parts=feature.impure_parts,
        properties_found=len(all_results),
        properties_verified=verified_count,
        properties_unverifiable=unverifiable_count,
        results=all_results,
    )


def run_feature_pipeline_from_file(
    file_path: str,
    language: str | None = None,
    check_fidelity: bool = False,
) -> FeaturePipelineResult:
    path = pathlib.Path(file_path)
    if not path.exists():
        raise FileNotFoundError(f"File not found: {file_path}")
    code = path.read_text()
    detected = language or _detect_language(path.suffix)
    return run_feature_pipeline(code, feature_file=str(path), language=detected, check_fidelity=check_fidelity)


_EXTENSION_MAP = {
    ".py": "Python",
    ".java": "Java",
    ".kt": "Kotlin",
    ".kts": "Kotlin",
    ".ts": "TypeScript",
    ".tsx": "TypeScript",
    ".js": "JavaScript",
    ".jsx": "JavaScript",
    ".mjs": "JavaScript",
    ".go": "Go",
    ".rs": "Rust",
    ".cs": "C#",
    ".cpp": "C++",
    ".cc": "C++",
    ".cxx": "C++",
    ".c": "C",
    ".h": "C",
    ".rb": "Ruby",
    ".zig": "Zig",
}


def _detect_language(suffix: str) -> str:
    return _EXTENSION_MAP.get(suffix.lower(), "unknown")
