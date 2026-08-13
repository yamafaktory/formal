import logging

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel, Field

from . import guide, specs
from . import session as sessions
from .session import PropertySpec

logger = logging.getLogger("formal.api")

app = FastAPI(title="formal", version="2.0.0")


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
    proofs: dict[str, str]


class FailureOut(BaseModel):
    id: str
    error: str
    line: int | None = None
    col: int | None = None
    hint: str = ""


class CheckResponse(BaseModel):
    verified: list[str]
    failed: list[FailureOut]
    remaining: list[str]
    complete: bool


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
    try:
        outcomes = sessions.check(session, req.proofs)
    except sessions.UnknownProperty as e:
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:
        logger.exception("Unhandled error in /session/check")
        raise HTTPException(status_code=500, detail=str(e))

    return CheckResponse(
        verified=[o.id for o in outcomes if o.verified],
        failed=[
            FailureOut(id=o.id, error=o.error, line=o.line, col=o.col, hint=o.hint) for o in outcomes if not o.verified
        ],
        remaining=session.work_ids,
        complete=session.complete,
    )


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
