//! The spec against the Rust it describes.

use std::{
    path::PathBuf,
    time::Duration,
};

use formal_core::{
    lean_spec::LeanSpec,
    pystr,
};
use formal_lean::{
    run::Runner,
    verifier::LeanResult,
};

const ALPHABET: [char; 15] = [
    'a', ' ', '\t', '\u{a0}', '\u{1f}', '\n', '\u{b}', '\u{c}', '\u{1c}', '\u{1d}', '\u{1e}', '\r',
    '\u{85}', '\u{2028}', '\u{2029}',
];

const LONGEST_WORD: usize = 4;

fn runner() -> Option<Runner> {
    let runner = Runner::from_env();
    let project = &runner.paths().lean_project_dir;
    (project.join("lakefile.toml").is_file() && project.join(".lake").is_dir()).then_some(runner)
}

fn repository() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn spec() -> LeanSpec {
    let path = repository().join("spec/Pystr.lean");
    LeanSpec::load(&path.to_string_lossy()).expect("the spec loads")
}

fn printed(result: &LeanResult) -> Vec<String> {
    result
        .output
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|message| message["severity"] == "information")
        .filter_map(|message| message["data"].as_str().map(str::to_string))
        .collect()
}

fn words(length: usize) -> Vec<String> {
    if length == 0 {
        return vec![String::new()];
    }
    let shorter = words(length - 1);
    ALPHABET
        .iter()
        .flat_map(|&c| shorter.iter().map(move |word| format!("{c}{word}")))
        .collect()
}

fn inputs() -> Vec<String> {
    (0..=LONGEST_WORD).flat_map(words).collect()
}

fn code_points(s: &str) -> String {
    format!("{:?}", s.chars().map(u32::from).collect::<Vec<_>>())
}

fn lines(s: &str) -> String {
    let lines: Vec<String> = pystr::splitlines(s).into_iter().map(code_points).collect();
    format!("[{}]", lines.join(", "))
}

fn evaluation(spec: &str) -> String {
    let alphabet: Vec<String> = ALPHABET
        .iter()
        .map(|&c| format!("Char.ofNat {}", u32::from(c)))
        .collect();
    format!(
        r"import Lean.Elab.Command
{spec}
def alphabet : List Char := [{alphabet}]

def words : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun c => (words n).map (c :: ·)

def inputs : List (List Char) := (List.range {longest}).flatMap words

def codePoints (s : List Char) : String := toString (s.map Char.toNat)

#eval do
  for n in [0:0x110000] do
    if Nat.isValidChar n && Pystr.isSpace (Char.ofNat n) then IO.println n

#eval do
  for s in inputs do IO.println (codePoints (Pystr.strip s))

#eval do
  for s in inputs do IO.println (codePoints (Pystr.rstrip s))

#eval do
  for s in inputs do IO.println (toString ((Pystr.splitlines s).map codePoints))
",
        alphabet = alphabet.join(", "),
        longest = LONGEST_WORD + 1,
    )
}

fn first_difference(name: &str, spec: &str, rust: &[(String, String)]) -> Option<String> {
    let spec: Vec<&str> = spec.lines().collect();
    if spec.len() != rust.len() {
        return Some(format!(
            "{name}: the spec answered {} inputs and the Rust {}",
            spec.len(),
            rust.len()
        ));
    }
    spec.iter()
        .zip(rust)
        .find(|(said, (_, answered))| *said != answered)
        .map(|(said, (input, answered))| {
            format!("{name} {input:?}: the spec says {said}, the Rust says {answered}")
        })
}

#[test]
fn the_rust_answers_what_the_spec_answers() {
    let Some(runner) = runner() else {
        return;
    };
    let result = runner.verify(&evaluation(&spec().text), Some(Duration::from_mins(5)));
    assert!(result.success, "{:?}", result.errors);
    let printed = printed(&result);
    let [space, strip, rstrip, splitlines] = printed.as_slice() else {
        panic!("expected four evaluations, got {}", printed.len());
    };

    let rust_space: Vec<String> = (0..=0x0010_ffff)
        .filter_map(char::from_u32)
        .filter(|&c| pystr::is_space(c))
        .map(|c| u32::from(c).to_string())
        .collect();
    let spec_space: Vec<&str> = space.lines().collect();
    assert_eq!(spec_space, rust_space, "is_space differs from the spec");

    let inputs = inputs();
    let answers = |f: &dyn Fn(&str) -> String| -> Vec<(String, String)> {
        inputs
            .iter()
            .map(|input| (input.clone(), f(input)))
            .collect()
    };
    let differences: Vec<String> = [
        first_difference("strip", strip, &answers(&|s| code_points(pystr::strip(s)))),
        first_difference(
            "rstrip",
            rstrip,
            &answers(&|s| code_points(pystr::rstrip(s))),
        ),
        first_difference("splitlines", splitlines, &answers(&lines)),
    ]
    .into_iter()
    .flatten()
    .collect();
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}
