import json
import logging
import pathlib

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

from .feature_pipeline import (
    FeaturePipelineResult,
    run_feature_pipeline,
    run_feature_pipeline_from_file,
)
from .pipeline import PipelineResult, run_pipeline

logger = logging.getLogger("formal.api")

app = FastAPI(title="Lean4 Verifier", version="1.0.0")


# ── /verify ───────────────────────────────────────────────────────────────────


class VerifyRequest(BaseModel):
    task: str
    save_result: bool = False


class StageOut(BaseModel):
    name: str
    output: str
    success: bool
    retries: int
    error: str


class VerifyResponse(BaseModel):
    task: str
    verified: bool
    stages: list[StageOut]
    lean_output: str
    lean_code: str


# ── /verify-feature ───────────────────────────────────────────────────────────


class VerifyFeatureRequest(BaseModel):
    code: str | None = None
    file: str | None = None
    filename: str | None = None  # display name when code is passed inline
    language: str | None = None  # auto-detected from file extension if omitted
    parallel: bool = True
    save_result: bool = False


class PropertyResultOut(BaseModel):
    property_id: str
    description: str
    kind: str
    function: str
    status: str  # "verified" | "failed" | "unverifiable"
    verified: bool
    lean_code: str
    lean_output: str
    retries: int
    reason: str


class VerifyFeatureResponse(BaseModel):
    feature_file: str
    feature_summary: str
    pure_functions: list[str]
    impure_parts: list[str]
    properties_found: int
    properties_verified: int
    properties_unverifiable: int
    overall_score: str
    results: list[PropertyResultOut]


# ── Endpoints ─────────────────────────────────────────────────────────────────


@app.get("/health")
def health():
    return {"status": "ok"}


@app.post("/verify", response_model=VerifyResponse)
def verify_task(req: VerifyRequest):
    try:
        result: PipelineResult = run_pipeline(req.task)
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))

    if req.save_result:
        _save(
            "verify",
            req.task[:40],
            {"task": result.task, "verified": result.verified, "stages": [s.__dict__ for s in result.stages]},
        )

    lean_code, lean_output = "", ""
    if result.stages:
        proof_stage = next((s for s in result.stages if s.name == "Proof generation"), None)
        if proof_stage:
            lean_code = proof_stage.output
    if result.lean_result:
        lean_output = result.lean_result.output

    return VerifyResponse(
        task=result.task,
        verified=result.verified,
        stages=[StageOut(**s.__dict__) for s in result.stages],
        lean_output=lean_output,
        lean_code=lean_code,
    )


@app.post("/verify-feature", response_model=VerifyFeatureResponse)
def verify_feature(req: VerifyFeatureRequest):
    if not req.code and not req.file:
        raise HTTPException(status_code=400, detail="Provide either 'code' or 'file'")

    try:
        if req.file:
            result: FeaturePipelineResult = run_feature_pipeline_from_file(req.file, language=req.language)
        else:
            result = run_feature_pipeline(
                req.code,
                parallel=req.parallel,
                language=req.language or "Python",
                feature_file=req.filename or "<inline>",
            )
    except FileNotFoundError as e:
        raise HTTPException(status_code=404, detail=str(e))
    except Exception as e:
        logger.exception("Unhandled error in /verify-feature")
        raise HTTPException(status_code=500, detail=str(e))

    if req.save_result:
        label = (req.file or "inline")[:40]
        _save(
            "feature",
            label,
            {
                "feature_file": result.feature_file,
                "verified": result.properties_verified,
                "total": result.properties_found,
                "results": [r.__dict__ for r in result.results],
            },
        )

    return VerifyFeatureResponse(
        feature_file=result.feature_file,
        feature_summary=result.feature_summary,
        pure_functions=result.pure_functions,
        impure_parts=result.impure_parts,
        properties_found=result.properties_found,
        properties_verified=result.properties_verified,
        properties_unverifiable=result.properties_unverifiable,
        overall_score=result.overall_score,
        results=[PropertyResultOut(**r.__dict__) for r in result.results],
    )


def _save(prefix: str, label: str, data: dict):
    pathlib.Path("/app/results").mkdir(exist_ok=True)
    safe = "".join(c if c.isalnum() else "_" for c in label)
    with open(f"/app/results/{prefix}_{safe}.json", "w") as f:
        json.dump(data, f, indent=2)
