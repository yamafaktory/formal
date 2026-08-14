//! Command-line entry point — runs the server and reports on the installation.

use std::{
    process::{
        Command,
        ExitCode,
    },
    sync::Arc,
};

use clap::{
    Parser,
    Subcommand,
};
use formal_lean::{
    env::{
        Env,
        parse_dotenv,
    },
    paths::Paths,
    process::{
        Endpoint,
        Server,
    },
};
use formal_server::AppState;

mod status;

use status::Status;

/// Property checker for code, backed by Lean 4. Agents drive it over HTTP.
#[derive(Debug, Parser)]
#[command(name = "formal", version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Action,
}

#[derive(Debug, Subcommand)]
enum Action {
    /// Show the resolved configuration and toolchain state.
    Status,

    /// Run the HTTP API.
    Serve {
        /// The interface to listen on.
        #[arg(long)]
        host: Option<String>,
        /// The port to listen on.
        #[arg(long)]
        port: Option<u16>,
        /// Start detached and return once the server answers.
        #[arg(long)]
        background: bool,
    },

    /// Stop a server started with --background.
    Stop {
        /// The interface it listens on.
        #[arg(long)]
        host: Option<String>,
        /// The port it listens on.
        #[arg(long)]
        port: Option<u16>,
    },
}

/// The exit code for a command that could not do what it was asked.
const FAILED: u8 = 1;

/// The exit code for a refusal that is the caller's to fix.
const REFUSED: u8 = 2;

fn endpoint(env: &Env, host: Option<String>, port: Option<u16>) -> Endpoint {
    let resolved = Endpoint::resolve(env);
    Endpoint {
        host: host.unwrap_or(resolved.host),
        port: port.unwrap_or(resolved.port),
    }
}

fn cmd_status(env: &Env, dotenv: &[(String, String)]) -> ExitCode {
    let status = Status::read(env, dotenv);
    println!("{}", status.render());
    if status.ready {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(FAILED)
    }
}

fn cmd_serve(env: &Env, host: Option<String>, port: Option<u16>, background: bool) -> ExitCode {
    let endpoint = endpoint(env, host, port);
    if endpoint.is_running() {
        println!("already serving on {}", endpoint.url());
        return ExitCode::SUCCESS;
    }

    let server = Server::new(endpoint.clone(), &Paths::resolve(env));
    if background {
        let Ok(exe) = std::env::current_exe() else {
            eprintln!("formal: could not find my own binary to start in the background");
            return ExitCode::from(FAILED);
        };
        let mut command = Command::new(exe);
        command.args([
            "serve",
            "--host",
            &endpoint.host,
            "--port",
            &endpoint.port.to_string(),
        ]);
        return match server.start(command, None) {
            Ok(url) => {
                println!("serving on {url} (log: {})", server.log_file().display());
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("formal: {e}");
                ExitCode::from(REFUSED)
            }
        };
    }

    let state = match AppState::resolve(env) {
        Ok(state) => Arc::new(state),
        Err(e) => {
            eprintln!("formal: {e}");
            return ExitCode::from(REFUSED);
        }
    };
    let runtime = match tokio::runtime::Runtime::new() {
        Ok(runtime) => runtime,
        Err(e) => {
            eprintln!("formal: {e}");
            return ExitCode::from(FAILED);
        }
    };
    println!("serving on {}", endpoint.url());
    match runtime.block_on(formal_server::serve(state, &endpoint.host, endpoint.port)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("formal: {e}");
            ExitCode::from(FAILED)
        }
    }
}

fn cmd_stop(env: &Env, host: Option<String>, port: Option<u16>) -> ExitCode {
    let endpoint = endpoint(env, host, port);
    let server = Server::new(endpoint.clone(), &Paths::resolve(env));
    if server.stop(None) {
        println!("stopped");
        return ExitCode::SUCCESS;
    }
    if endpoint.is_running() {
        eprintln!(
            "something is serving on {} but formal did not start it",
            endpoint.url()
        );
        return ExitCode::from(FAILED);
    }
    println!("not running");
    ExitCode::SUCCESS
}

fn main() -> ExitCode {
    // The .env is read before anything asks a question of the configuration, and
    // fills in only what the environment did not already answer.
    let home = Paths::from_env().formal_home;
    let dotenv = parse_dotenv(&std::fs::read_to_string(home.join(".env")).unwrap_or_default());
    let env = Env::with_dotenv(&home.join(".env"));

    match Cli::parse().command {
        Action::Status => cmd_status(&env, &dotenv),
        Action::Serve {
            host,
            port,
            background,
        } => cmd_serve(&env, host, port, background),
        Action::Stop { host, port } => cmd_stop(&env, host, port),
    }
}
