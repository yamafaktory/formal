//! What `formal status` reports, as data rather than as printing.
//!
//! Separated so the rows can be tested. The Python version printed as it went,
//! which meant the only way to check it was to read it.

use formal_lean::{
    env::Env,
    paths::Paths,
    process::Server,
    sandbox::Sandbox,
    toolchain::Toolchain,
};

/// Every key formal understands.
///
/// A key outside this set is reported by `formal status`: something in `.env` that
/// nothing reads is a misconfiguration that otherwise says nothing at all.
pub(crate) const KNOWN_ENV_KEYS: [&str; 13] = [
    "ELAN_HOME",
    "FORMAL_HOME",
    "FORMAL_HOST",
    "FORMAL_PORT",
    "FORMAL_RESULTS_DIR",
    "FORMAL_SANDBOX",
    "LEAN_PROJECT_DIR",
    "LEAN_TIMEOUT",
    "NO_COLOR",
    "PROOF_CACHE_DIR",
    "PROOF_CACHE_TTL_DAYS",
    "SESSION_TTL_MINUTES",
    "XDG_DATA_HOME",
];

/// Keys a `.env` sets that nothing reads — a silent misconfiguration.
#[must_use]
pub(crate) fn unknown_env_keys(dotenv: &[(String, String)]) -> Vec<String> {
    let mut unknown: Vec<String> = dotenv
        .iter()
        .map(|(key, _)| key.clone())
        .filter(|key| !KNOWN_ENV_KEYS.contains(&key.as_str()))
        .collect();
    unknown.sort();
    unknown.dedup();
    unknown
}

/// What formal is configured to do, and whether it can do it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Status {
    /// The name and value of each thing worth reporting.
    pub(crate) rows: Vec<(String, String)>,
    /// Whether Lean is installed and Mathlib is built.
    pub(crate) ready: bool,
}

impl Status {
    /// Read the state of the installation.
    #[must_use]
    pub(crate) fn read(env: &Env, dotenv: &[(String, String)]) -> Self {
        let paths = Paths::resolve(env);
        let toolchain = Toolchain::resolve(env);
        let sandbox = Sandbox::resolve(env, &paths, &toolchain);
        let server = Server::new(formal_lean::process::Endpoint::resolve(env), &paths);

        let lake = toolchain.which("lake");
        let toolchain_file = paths.lean_project_dir.join("lean-toolchain");
        let mathlib = mathlib_lib(&paths);
        let ready = lake.is_some() && mathlib.is_dir();

        let mut rows = vec![
            ("home".to_string(), paths.formal_home.display().to_string()),
            (
                "lean project".to_string(),
                paths.lean_project_dir.display().to_string(),
            ),
            (
                "proof cache".to_string(),
                paths.proof_cache_dir.display().to_string(),
            ),
            (
                "lake".to_string(),
                lake.map_or_else(
                    || "not on PATH".to_string(),
                    |path| path.display().to_string(),
                ),
            ),
            (
                "lean toolchain".to_string(),
                std::fs::read_to_string(&toolchain_file)
                    .map_or_else(|_| "missing".to_string(), |text| text.trim().to_string()),
            ),
            (
                "mathlib oleans".to_string(),
                if mathlib.is_dir() {
                    "built".to_string()
                } else {
                    "missing — run: formal setup".to_string()
                },
            ),
            ("lean sandbox".to_string(), sandbox.describe()),
            (
                "server".to_string(),
                format!(
                    "{} ({})",
                    server.endpoint.url(),
                    if server.endpoint.is_running() {
                        "running"
                    } else {
                        "not running"
                    }
                ),
            ),
        ];

        let unknown = unknown_env_keys(dotenv);
        if !unknown.is_empty() {
            rows.push((
                "unused .env keys".to_string(),
                format!("{} — nothing reads these", unknown.join(", ")),
            ));
        }

        Self { rows, ready }
    }

    /// The rows as they are printed, lined up on the longest name.
    #[must_use]
    pub(crate) fn render(&self) -> String {
        let width = self
            .rows
            .iter()
            .map(|(name, _)| name.chars().count())
            .max()
            .unwrap_or(0);
        self.rows
            .iter()
            .map(|(name, value)| format!("{name:width$}  {value}"))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

/// Where Mathlib's compiled oleans land once `formal setup` has run.
#[must_use]
pub(crate) fn mathlib_lib(paths: &Paths) -> std::path::PathBuf {
    paths
        .lean_project_dir
        .join(".lake/packages/mathlib/.lake/build/lib")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dotenv(keys: &[&str]) -> Vec<(String, String)> {
        keys.iter()
            .map(|key| ((*key).to_string(), "x".to_string()))
            .collect()
    }

    #[test]
    fn a_key_nothing_reads_is_reported() {
        assert_eq!(
            unknown_env_keys(&dotenv(&["OPENAI_API_KEY"])),
            ["OPENAI_API_KEY"]
        );
    }

    #[test]
    fn every_key_formal_understands_is_accepted() {
        assert!(unknown_env_keys(&dotenv(&KNOWN_ENV_KEYS)).is_empty());
    }

    #[test]
    fn the_unknown_keys_are_sorted_and_deduplicated() {
        let repeated = dotenv(&["ZZZ", "AAA", "ZZZ"]);
        assert_eq!(unknown_env_keys(&repeated), ["AAA", "ZZZ"]);
    }

    #[test]
    fn the_rows_name_where_everything_lives() {
        let env = Env::from_pairs([("FORMAL_HOME", "/srv/formal"), ("FORMAL_SANDBOX", "off")]);
        let status = Status::read(&env, &[]);
        let named: Vec<&str> = status.rows.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(
            named,
            [
                "home",
                "lean project",
                "proof cache",
                "lake",
                "lean toolchain",
                "mathlib oleans",
                "lean sandbox",
                "server",
            ]
        );
        let by_name = |wanted: &str| {
            status
                .rows
                .iter()
                .find(|(name, _)| name == wanted)
                .map(|(_, value)| value.clone())
                .unwrap_or_default()
        };
        assert_eq!(by_name("home"), "/srv/formal");
        assert_eq!(by_name("lean sandbox"), "off (FORMAL_SANDBOX)");
    }

    #[test]
    fn a_missing_installation_is_not_ready_and_says_what_to_run() {
        let env = Env::from_pairs([("FORMAL_HOME", "/nowhere"), ("ELAN_HOME", "/nowhere/elan")]);
        let status = Status::read(&env, &[]);
        assert!(!status.ready);
        assert!(
            status.render().contains("missing — run: formal setup"),
            "{}",
            status.render()
        );
    }

    #[test]
    fn an_unused_key_becomes_a_row_of_its_own() {
        let env = Env::from_pairs([("FORMAL_HOME", "/srv/formal")]);
        let status = Status::read(&env, &dotenv(&["LLM_BACKEND"]));
        assert!(
            status
                .render()
                .contains("LLM_BACKEND — nothing reads these"),
            "{}",
            status.render()
        );
    }

    #[test]
    fn the_rows_line_up_on_the_longest_name() {
        let status = Status {
            rows: vec![
                ("home".to_string(), "/a".to_string()),
                ("lean toolchain".to_string(), "/b".to_string()),
            ],
            ready: true,
        };
        assert_eq!(status.render(), "home            /a\nlean toolchain  /b");
    }
}
