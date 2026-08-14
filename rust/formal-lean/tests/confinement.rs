//! The sandbox exercised against a real bubblewrap, not just inspected.
//!
//! Every other test reads the command that would be run. These run it. An argv
//! that looks right and confines nothing is the failure worth catching, and it is
//! invisible from the argv alone.
//!
//! Each test does nothing when bubblewrap is not installed — there is no verdict
//! to give on a machine that cannot sandbox in the first place.

use std::{
    ffi::OsString,
    path::PathBuf,
    process::Command,
};

use formal_lean::{
    paths::Paths,
    sandbox::{
        Mode,
        Sandbox,
    },
    toolchain::Toolchain,
};

fn bwrap() -> Option<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
        .map(|dir| dir.join("bwrap"))
        .find(|candidate| candidate.is_file())
}

fn lean_project_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean_project")
}

/// Run `argv` confined, or return nothing when there is no bubblewrap to confine it.
fn confined(argv: &[&str]) -> Option<std::process::Output> {
    let bwrap = bwrap()?;
    let paths = Paths::under(lean_project_dir().parent()?.to_path_buf());
    let toolchain = Toolchain::new(
        std::env::var_os("HOME").map(PathBuf::from)?.join(".elan"),
        &std::env::var_os("PATH").unwrap_or_else(|| OsString::from("/usr/bin")),
    );
    let wrapped = Sandbox::new(Mode::Required, Some(bwrap), &paths, &toolchain)
        .wrap(argv)
        .expect("bubblewrap was found");
    let mut command = Command::new(&wrapped.argv[0]);
    command.args(&wrapped.argv[1..]);
    Some(command.output().expect("bubblewrap runs"))
}

#[test]
fn the_home_directory_is_not_readable() {
    let secret = std::env::var_os("HOME")
        .map(PathBuf::from)
        .map(|home| home.join(".bashrc"));
    let Some(secret) = secret.filter(|path| path.is_file()) else {
        return;
    };
    let Some(output) = confined(&["cat", &secret.to_string_lossy()]) else {
        return;
    };
    assert!(
        !output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn the_network_is_unreachable() {
    let Some(output) = confined(&[
        "python3",
        "-c",
        "import socket; socket.create_connection(('1.1.1.1', 443), 5)",
    ]) else {
        return;
    };
    assert!(!output.status.success());
}

#[test]
fn the_lean_project_is_readable() {
    let toolchain_file = lean_project_dir().join("lean-toolchain");
    if !toolchain_file.is_file() {
        return;
    }
    let Some(output) = confined(&["cat", &toolchain_file.to_string_lossy()]) else {
        return;
    };
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("leanprover"));
}
