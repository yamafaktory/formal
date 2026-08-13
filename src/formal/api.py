import logging
from importlib.metadata import PackageNotFoundError
from importlib.metadata import version as _installed_version

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel, Field

from . import guide, specs
from . import session as sessions
from .session import PropertySpec

logger = logging.getLogger("formal.api")


def _version() -> str:
    """Read from the installed metadata — a second copy here drifted from pyproject once."""
    try:
        return _installed_version("formal")
    except PackageNotFoundError:
        return "0+unknown"


app = FastAPI(title="formal", version=_version())


# ── /session ──────────────────────────────────────────────────────────────────


class PropertySpecIn(BaseModel):
    id: str
    description: str
    kind: str = ""
    function: str = ""
    function_code: str = ""
    formal: str = ""
    preconditions: list[str] = Field(default_factory=list)
    assumptions: list[str] = Field(default_factory=list)


class SessionRequest(BaseModel):
    properties: list[PropertySpecIn] = Field(default_factory=list)
    spec_file: str | None = None
    root: str | None = None  # resolves each spec's source_file; defaults to the spec file's directory


class CacheHitOut(BaseModel):
    id: str
    description: str
    kind: str
    assumptions: list[str] = Field(default_factory=list)


class SessionResponse(BaseModel):
    session_id: str
    cached: list[CacheHitOut]
    work: list[str]
    complete: bool
    stale: list[str] = Field(default_factory=list)


class CheckRequest(BaseModel):
    proofs: dict[str, str] = Field(default_factory=dict)
    # Absolute paths to .lean files, read by the server. Every caller so far wrote a
    # script to load these and escape them into `proofs`; this removes the need.
    proof_files: dict[str, str] = Field(default_factory=dict)


class FailureOut(BaseModel):
    id: str
    error: str
    line: int | None = None
    col: int | None = None
    hint: str = ""


class CheckResponse(BaseModel):
    verified: list[str]
    # Verified ids whose accepted proof is not the one you sent — the recovery chain
    # found another. Fetch it from /session/{id}/proof/{property_id}.
    recovered: list[str] = Field(default_factory=list)
    failed: list[FailureOut]
    remaining: list[str]
    complete: bool


class ProofOut(BaseModel):
    id: str
    origin: str  # "submitted" | "recovered" | "cache"
    lean_code: str


# ── Endpoints ─────────────────────────────────────────────────────────────────


@app.get("/health")
def health():
    return {"status": "ok"}


@app.get("/guide")
def read_guide():
    return guide.index()


@app.get("/guide/{topic}")
def read_guide_topic(topic: str):
    try:
        return {"topic": topic, "instructions": guide.topic(topic)}
    except KeyError:
        raise HTTPException(status_code=404, detail=f"No such topic: {topic}. Try: {', '.join(guide.TOPICS)}")


@app.post("/session", response_model=SessionResponse)
def open_session(req: SessionRequest):
    if bool(req.properties) == bool(req.spec_file):
        raise HTTPException(status_code=400, detail="Provide either 'properties' or 'spec_file', not both")

    if req.spec_file:
        try:
            loaded = specs.load(req.spec_file, root=req.root)
        except specs.SpecError as e:
            raise HTTPException(status_code=400, detail=str(e))
        session = sessions.create(loaded.specs, stale=loaded.stale_ids)
    else:
        ids = [p.id for p in req.properties]
        duplicates = sorted({pid for pid in ids if ids.count(pid) > 1})
        if duplicates:
            raise HTTPException(status_code=400, detail=f"Duplicate property ids: {', '.join(duplicates)}")
        session = sessions.create([PropertySpec(**p.model_dump()) for p in req.properties])
    return SessionResponse(
        session_id=session.id,
        cached=[CacheHitOut(**vars(session.hits[pid])) for pid in session.cached_ids if pid in session.hits],
        work=session.work_ids,
        complete=session.complete,
        stale=session.stale,
    )


@app.get("/session/{session_id}", response_model=SessionResponse)
def read_session(session_id: str):
    session = _require(session_id)
    return SessionResponse(
        session_id=session.id,
        cached=[CacheHitOut(**vars(session.hits[pid])) for pid in session.cached_ids if pid in session.hits],
        work=session.work_ids,
        complete=session.complete,
        stale=session.stale,
    )


@app.post("/session/{session_id}/check", response_model=CheckResponse)
def check_session(session_id: str, req: CheckRequest):
    session = _require(session_id)
    if bool(req.proofs) == bool(req.proof_files):
        raise HTTPException(status_code=400, detail="Provide either 'proofs' or 'proof_files', not both")

    try:
        proofs = req.proofs or specs.read_proofs(req.proof_files)
    except specs.SpecError as e:
        raise HTTPException(status_code=400, detail=str(e))

    try:
        outcomes = sessions.check(session, proofs)
    except sessions.UnknownProperty as e:
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:
        logger.exception("Unhandled error in /session/check")
        raise HTTPException(status_code=500, detail=str(e))

    return CheckResponse(
        verified=[o.id for o in outcomes if o.verified],
        recovered=[o.id for o in outcomes if o.verified and o.recovered],
        failed=[
            FailureOut(id=o.id, error=o.error, line=o.line, col=o.col, hint=o.hint) for o in outcomes if not o.verified
        ],
        remaining=session.work_ids,
        complete=session.complete,
    )


@app.get("/session/{session_id}/proof/{property_id:path}", response_model=ProofOut)
def read_proof(session_id: str, property_id: str):
    """The proof Lean actually accepted, which is also the one that was cached.

    property_id takes the rest of the path. The guide recommends ids shaped
    `function/property`, and without this the endpoint was unreachable for every id
    that followed that advice — percent-encoding does not help, since the path is
    decoded before routing.
    """
    session = _require(session_id)
    if property_id not in session.specs:
        raise HTTPException(status_code=404, detail=f"Not registered in this session: {property_id}")
    lean_code = session.verified.get(property_id)
    if lean_code is None:
        raise HTTPException(status_code=404, detail=f"Nothing accepted yet for {property_id}")
    return ProofOut(id=property_id, origin=session.origin(property_id), lean_code=lean_code)


@app.delete("/session/{session_id}")
def close_session(session_id: str):
    if not sessions.drop(session_id):
        raise HTTPException(status_code=404, detail=f"No such session: {session_id}")
    return {"status": "closed"}


def _require(session_id: str):
    session = sessions.get(session_id)
    if session is None:
        raise HTTPException(status_code=404, detail=f"No such session: {session_id}")
    return session
