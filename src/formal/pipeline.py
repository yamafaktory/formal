import os
from dataclasses import dataclass

from . import prompts
from .lean_verifier import LeanResult, verify
from .llm_client import call_llm, extract_code_block


@dataclass
class StageResult:
    name: str
    output: str
    success: bool
    retries: int
    error: str = ""


@dataclass
class PipelineResult:
    task: str
    verified: bool
    stages: list[StageResult]
    lean_result: LeanResult | None = None


def run_pipeline(task: str) -> PipelineResult:
    """
    Task-level pipeline:
      1. Generate Python code for the task
      2. Extract a formal specification
      3. Autoformalize to Lean 4 + generate proof (with retries)
    """
    stages: list[StageResult] = []
    max_retries = int(os.getenv("MAX_PROOF_RETRIES", "3"))

    # ── Stage 1: Generate Python code ────────────────────────────────────────
    raw = call_llm(
        prompts.CODE_GENERATION_SYSTEM,
        prompts.CODE_GENERATION_USER.format(task=task),
    )
    python_code = extract_code_block(raw, "python") or raw.strip()
    stages.append(
        StageResult(
            name="Code generation",
            output=python_code,
            success=bool(python_code),
            retries=0,
        )
    )

    # ── Stage 2: Extract formal spec ─────────────────────────────────────────
    raw = call_llm(
        prompts.SPEC_EXTRACTION_SYSTEM,
        prompts.SPEC_EXTRACTION_USER.format(code=python_code),
    )
    spec = raw.strip()
    stages.append(
        StageResult(
            name="Spec extraction",
            output=spec,
            success=bool(spec),
            retries=0,
        )
    )

    # ── Stage 3: Autoformalize + prove (with retries) ─────────────────────────
    lean_code = ""
    lean_result: LeanResult | None = None
    proof_retries = 0

    for attempt in range(max_retries):
        # Autoformalize
        if attempt == 0:
            raw = call_llm(
                prompts.AUTOFORMALIZE_SYSTEM,
                prompts.AUTOFORMALIZE_USER.format(spec=spec),
            )
        else:
            err = lean_result.first_error or {}
            raw = call_llm(
                prompts.AUTOFORMALIZE_SYSTEM,
                prompts.AUTOFORMALIZE_RETRY_USER.format(
                    error=err.get("data", "unknown error"),
                    previous=lean_code,
                ),
            )
            proof_retries += 1

        lean_code = extract_code_block(raw, "lean4") or extract_code_block(raw, "lean") or raw.strip()

        # Proof generation
        proof_raw = call_llm(
            prompts.PROOF_GENERATION_SYSTEM,
            prompts.PROOF_GENERATION_USER.format(theorem=lean_code),
        )
        lean_code = extract_code_block(proof_raw, "lean4") or extract_code_block(proof_raw, "lean") or lean_code

        lean_result = verify(lean_code)
        if lean_result.success:
            break

    stages.append(
        StageResult(
            name="Proof generation",
            output=lean_code,
            success=lean_result.success if lean_result else False,
            retries=proof_retries,
            error=lean_result.output if lean_result and not lean_result.success else "",
        )
    )

    return PipelineResult(
        task=task,
        verified=lean_result.success if lean_result else False,
        stages=stages,
        lean_result=lean_result,
    )
