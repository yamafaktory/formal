//! Serve formal over HTTP.
//!
//! Argument handling is deliberately minimal here — `formal serve` is the front
//! door and has not been ported yet. This exists so the conformance suite has
//! something to point at.

use std::{
    net::SocketAddr,
    sync::Arc,
};

use formal_lean::logger::{
    Tag,
    log,
};
use formal_server::{
    AppState,
    router,
};

const DEFAULT_PORT: u16 = 8000;

fn port() -> u16 {
    std::env::args()
        .nth(1)
        .or_else(|| std::env::var("FORMAL_PORT").ok())
        .and_then(|value| value.trim().parse().ok())
        .unwrap_or(DEFAULT_PORT)
}

#[tokio::main]
async fn main() -> std::process::ExitCode {
    let state = match AppState::from_env() {
        Ok(state) => Arc::new(state),
        Err(e) => {
            log(Tag::Fail, &e.to_string());
            return std::process::ExitCode::FAILURE;
        }
    };

    let address = SocketAddr::from(([127, 0, 0, 1], port()));
    let listener = match tokio::net::TcpListener::bind(address).await {
        Ok(listener) => listener,
        Err(e) => {
            log(Tag::Fail, &format!("could not listen on {address} — {e}"));
            return std::process::ExitCode::FAILURE;
        }
    };

    log(
        Tag::Pipeline,
        &format!("formal listening on http://{address}"),
    );
    if let Err(e) = axum::serve(listener, router(state))
        .with_graceful_shutdown(async {
            let _ = tokio::signal::ctrl_c().await;
        })
        .await
    {
        log(Tag::Fail, &e.to_string());
        return std::process::ExitCode::FAILURE;
    }
    std::process::ExitCode::SUCCESS
}
