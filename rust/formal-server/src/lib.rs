//! formal's HTTP surface.
//!
//! What this must answer is stated without reference to any implementation in
//! `tests/conformance/`, and `golden/responses.json` says what each request gets
//! back. That file is the contract; this is one way of satisfying it.

use std::sync::Arc;

use axum::{
    Json,
    Router,
    extract::{
        Path,
        State,
    },
    http::StatusCode,
    response::{
        IntoResponse,
        Response,
    },
    routing::{
        get,
        post,
    },
};
use formal_core::{
    guide,
    hints::Table,
    property::PropertySpec,
    specs,
};
use formal_lean::{
    paths::Paths,
    run::Runner,
};
use formal_service::{
    cache::ProofCache,
    checker::Checker,
    session::{
        Session,
        Sessions,
    },
};
use serde::Serialize;

mod wire;

pub use wire::{
    CacheHitOut,
    CheckRequest,
    CheckResponse,
    FailureOut,
    ProofOut,
    PropertySpecIn,
    SessionRequest,
    SessionResponse,
};

/// Everything a request might need, built once at startup.
#[derive(Debug)]
pub struct AppState {
    /// The open sessions.
    pub sessions: Sessions,
    /// Where accepted proofs are kept.
    pub cache: ProofCache,
    /// How Lean is invoked.
    pub runner: Runner,
    /// The advice for a rejected proof.
    pub table: &'static Table,
}

impl AppState {
    /// State built from parts rather than from the environment.
    ///
    /// # Errors
    ///
    /// The shipped hint table failing to parse.
    pub fn new(
        sessions: Sessions,
        cache: ProofCache,
        runner: Runner,
    ) -> Result<Self, formal_core::hints::HintTableError> {
        Ok(Self {
            sessions,
            cache,
            runner,
            table: Table::shipped()?,
        })
    }

    /// The state this process would run with.
    ///
    /// # Errors
    ///
    /// The shipped hint table failing to parse, which is a build-time mistake
    /// rather than anything a caller did.
    pub fn from_env() -> Result<Self, formal_core::hints::HintTableError> {
        let paths = Paths::from_env();
        Ok(Self {
            sessions: Sessions::from_env(),
            cache: ProofCache::from_env(&paths),
            runner: Runner::from_env(),
            table: Table::shipped()?,
        })
    }
}

/// A refusal, in the shape every one of formal's refusals has.
#[derive(Debug)]
pub struct ApiError {
    status: StatusCode,
    detail: String,
}

#[derive(Serialize)]
struct Detail {
    detail: String,
}

impl ApiError {
    fn new(status: StatusCode, detail: impl Into<String>) -> Self {
        Self {
            status,
            detail: detail.into(),
        }
    }

    fn bad_request(detail: impl Into<String>) -> Self {
        Self::new(StatusCode::BAD_REQUEST, detail)
    }

    fn not_found(detail: impl Into<String>) -> Self {
        Self::new(StatusCode::NOT_FOUND, detail)
    }

    fn no_such_session(session_id: &str) -> Self {
        Self::not_found(format!("No such session: {session_id}"))
    }
}

impl IntoResponse for ApiError {
    fn into_response(self) -> Response {
        (
            self.status,
            Json(Detail {
                detail: self.detail,
            }),
        )
            .into_response()
    }
}

type ApiResult<T> = Result<Json<T>, ApiError>;

/// Every route formal serves.
pub fn router(state: Arc<AppState>) -> Router {
    Router::new()
        .route("/health", get(health))
        .route("/guide", get(read_guide))
        .route("/guide/{topic}", get(read_guide_topic))
        .route("/session", post(open_session))
        .route(
            "/session/{session_id}",
            get(read_session).delete(close_session),
        )
        .route("/session/{session_id}/check", post(check_session))
        .route(
            "/session/{session_id}/proof/{*property_id}",
            get(read_proof),
        )
        .with_state(state)
}

#[derive(Serialize)]
struct Status {
    status: &'static str,
}

async fn health() -> Json<Status> {
    Json(Status { status: "ok" })
}

async fn read_guide() -> Json<serde_json::Value> {
    Json(guide::index())
}

#[derive(Serialize)]
struct TopicOut {
    topic: String,
    instructions: String,
}

async fn read_guide_topic(Path(topic): Path<String>) -> ApiResult<TopicOut> {
    let Some(instructions) = guide::topic(&topic) else {
        return Err(ApiError::not_found(format!(
            "No such topic: {topic}. Try: {}",
            guide::topic_names().join(", ")
        )));
    };
    Ok(Json(TopicOut {
        topic,
        instructions,
    }))
}

fn describe(session: &Session) -> SessionResponse {
    SessionResponse {
        session_id: session.id.clone(),
        cached: session
            .cached_ids()
            .into_iter()
            .filter_map(|id| session.hits.get(id))
            .map(|hit| CacheHitOut {
                id: hit.id.clone(),
                description: hit.description.clone(),
                kind: hit.kind.clone(),
                assumptions: hit.assumptions.clone(),
            })
            .collect(),
        work: session
            .work_ids()
            .into_iter()
            .map(ToString::to_string)
            .collect(),
        complete: session.complete(),
        stale: session.stale.clone(),
    }
}

async fn open_session(
    State(state): State<Arc<AppState>>,
    Json(req): Json<SessionRequest>,
) -> ApiResult<SessionResponse> {
    if req.properties.is_empty() == req.spec_file.is_none() {
        return Err(ApiError::bad_request(
            "Provide either 'properties' or 'spec_file', not both",
        ));
    }

    let (specs, stale_ids) = if let Some(spec_file) = &req.spec_file {
        let loaded = specs::load(spec_file, req.root.as_ref().map(std::path::Path::new))
            .map_err(|e| ApiError::bad_request(e.to_string()))?;
        let reported = loaded
            .stale_ids()
            .into_iter()
            .map(ToString::to_string)
            .collect();
        (loaded.specs().into_iter().cloned().collect(), reported)
    } else {
        let ids: Vec<&str> = req
            .properties
            .iter()
            .map(|property| property.id.as_str())
            .collect();
        let mut duplicates: Vec<&str> = ids
            .iter()
            .filter(|id| ids.iter().filter(|other| other == id).count() > 1)
            .copied()
            .collect();
        duplicates.sort_unstable();
        duplicates.dedup();
        if !duplicates.is_empty() {
            return Err(ApiError::bad_request(format!(
                "Duplicate property ids: {}",
                duplicates.join(", ")
            )));
        }
        let specs: Vec<PropertySpec> = req
            .properties
            .iter()
            .map(PropertySpecIn::into_spec)
            .collect();
        (specs, Vec::new())
    };

    let session = state.sessions.open(&state.cache, specs, stale_ids);
    let session = session.lock().map_err(|_| poisoned())?;
    Ok(Json(describe(&session)))
}

async fn read_session(
    State(state): State<Arc<AppState>>,
    Path(session_id): Path<String>,
) -> ApiResult<SessionResponse> {
    let session = state
        .sessions
        .get(&session_id)
        .ok_or_else(|| ApiError::no_such_session(&session_id))?;
    let session = session.lock().map_err(|_| poisoned())?;
    Ok(Json(describe(&session)))
}

async fn check_session(
    State(state): State<Arc<AppState>>,
    Path(session_id): Path<String>,
    Json(req): Json<CheckRequest>,
) -> ApiResult<CheckResponse> {
    let session = state
        .sessions
        .get(&session_id)
        .ok_or_else(|| ApiError::no_such_session(&session_id))?;

    if req.proofs.is_empty() == req.proof_files.is_empty() {
        return Err(ApiError::bad_request(
            "Provide either 'proofs' or 'proof_files', not both",
        ));
    }

    let proofs: Vec<(String, String)> = if req.proofs.is_empty() {
        let paths: Vec<(String, String)> = req.proof_files.into_iter().collect();
        specs::read_proofs(&paths).map_err(|e| ApiError::bad_request(e.to_string()))?
    } else {
        req.proofs.into_iter().collect()
    };

    // Lean is slow and blocking, and the session lock is held for the whole run, so
    // this belongs off the async runtime rather than on it.
    tokio::task::spawn_blocking(move || {
        let mut session = session.lock().map_err(|_| poisoned())?;
        let checker = Checker::new(&state.runner, state.table);
        let outcomes = session
            .check(&checker, &state.cache, &proofs)
            .map_err(|e| ApiError::bad_request(e.to_string()))?;
        Ok(Json(CheckResponse::of(&outcomes, &session)))
    })
    .await
    .map_err(|e| ApiError::new(StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?
}

async fn read_proof(
    State(state): State<Arc<AppState>>,
    Path((session_id, property_id)): Path<(String, String)>,
) -> ApiResult<ProofOut> {
    let session = state
        .sessions
        .get(&session_id)
        .ok_or_else(|| ApiError::no_such_session(&session_id))?;
    let session = session.lock().map_err(|_| poisoned())?;

    if !session.specs.iter().any(|spec| spec.id == property_id) {
        return Err(ApiError::not_found(format!(
            "Not registered in this session: {property_id}"
        )));
    }
    let lean_code = session
        .verified
        .get(&property_id)
        .ok_or_else(|| ApiError::not_found(format!("Nothing accepted yet for {property_id}")))?;

    Ok(Json(ProofOut {
        origin: session.origin(&property_id).as_str().to_string(),
        id: property_id,
        lean_code: lean_code.clone(),
    }))
}

async fn close_session(
    State(state): State<Arc<AppState>>,
    Path(session_id): Path<String>,
) -> ApiResult<Status> {
    if state.sessions.close(&session_id) {
        Ok(Json(Status { status: "closed" }))
    } else {
        Err(ApiError::no_such_session(&session_id))
    }
}

fn poisoned() -> ApiError {
    ApiError::new(
        StatusCode::INTERNAL_SERVER_ERROR,
        "A previous request left this session in an unknown state",
    )
}
