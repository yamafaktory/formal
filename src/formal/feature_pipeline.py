import os
import pathlib
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass

from .feature_extractor import (
    Property,
    decompose,
    extract_properties,
)
from .logger import get_logger, log
from .property_verifier import PropertyResult, unverifiable_result, verify_property

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
    def overall_score(self) -> str:
        verifiable_count = self.properties_found - self.properties_unverifiable
        if verifiable_count == 0:
            return "no_pure_logic"
        pct = self.properties_verified / verifiable_count
        if pct == 1.0:
            return "full"
        if pct >= 0.5:
            return "partial"
        return "failed"

    def summary(self) -> str:
        rule = "─" * 41
        score = (
            f"{self.overall_score}  ({self.properties_verified}/{self.properties_found} verified, "
            f"{self.properties_unverifiable} unverifiable)"
        )
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
        lines.append(rule)
        return "\n".join(lines)


def run_feature_pipeline(
    code: str,
    feature_file: str = "<inline>",
    parallel: bool = True,
    language: str = "Python",
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

    def _verify_one(prop: Property) -> PropertyResult:
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

        try:
            return verify_property(prop, fn, max_retries=max_retries, language=language)
        except Exception as e:
            log(_log, "FAIL", f"{prop.id} ✗ unexpected error: {e}")
            return PropertyResult(
                property_id=prop.id,
                description=prop.description,
                kind=prop.kind,
                function=prop.function,
                verified=False,
                lean_code="",
                lean_output=str(e),
                retries=0,
                reason=f"Unexpected error: {e}",
                status="failed",
            )

    verified_results: list[PropertyResult] = []

    if parallel and len(verifiable) > 1:
        workers = min(len(verifiable), int(os.getenv("MAX_PARALLEL_PROPERTIES", "4")))
        with ThreadPoolExecutor(max_workers=workers) as ex:
            futures = {ex.submit(_verify_one, p): p for p in verifiable}
            for future in as_completed(futures):
                verified_results.append(future.result())
    else:
        verified_results = [_verify_one(p) for p in verifiable]

    # Merge and sort back to original property order
    all_results = verified_results + unverifiable_results
    order = {p.id: i for i, p in enumerate(properties)}
    all_results.sort(key=lambda r: order.get(r.property_id, 999))

    verified_count = sum(1 for r in all_results if r.status == "verified")
    unverifiable_count = sum(1 for r in all_results if r.status == "unverifiable")
    failed_count = sum(1 for r in all_results if r.status == "failed")
    elapsed = time.monotonic() - _t0
    m, s = divmod(int(elapsed), 60)
    elapsed_str = f"{m}m {s}s" if m else f"{s}s"
    log(
        _log,
        "PIPELINE",
        f"Done — verified: {verified_count}, failed: {failed_count}, unverifiable: {unverifiable_count}"
        f" — total: {elapsed_str}",
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


def run_feature_pipeline_from_file(file_path: str, language: str | None = None) -> FeaturePipelineResult:
    path = pathlib.Path(file_path)
    if not path.exists():
        raise FileNotFoundError(f"File not found: {file_path}")
    code = path.read_text()
    detected = language or _detect_language(path.suffix)
    return run_feature_pipeline(code, feature_file=str(path), language=detected)


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
