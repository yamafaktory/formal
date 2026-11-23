//! A spec written in Lean, and the file formal checks a proof of it in.

use std::{
    collections::HashMap,
    fs,
    path::{
        Path,
        PathBuf,
    },
    sync::OnceLock,
};

use regex::Regex;

use crate::{
    lean_text::{
        Import,
        imports,
        runs_code,
        without_comments,
    },
    proof_cache::{
        lean_spec_answers_key,
        lean_spec_key,
        lean_spec_search_key,
    },
    property::PropertySpec,
    specs::{
        SpecError,
        expanduser,
        require_absolute,
    },
};

/// The command, defined before every proof, that requires `<id>.holds` to state `<id>`.
pub const HOLDS_COMMAND: &str = "#formal_holds";

/// What starts each line the evaluation prints, before the function and its answers.
pub const COMPARE_MARK: &str = "formal-compare";

const EVALUATION_IMPORT: &str = "Lean.Data.Json";

const ENCODING: &str = "namespace FormalCompare
scoped instance (priority := high) : Lean.ToJson Char := ⟨fun c => Lean.Json.str (String.singleton c)⟩
scoped instance (priority := high) : Lean.ToJson (List Char) := ⟨fun s => Lean.Json.str (String.ofList s)⟩
end FormalCompare";

const SEARCH_IMPORT: &str = "Plausible";

const ALWAYS: &str = "always";

const SEARCH_HELPERS: &str = "namespace FormalRefute
open Plausible

scoped instance (priority := high) {n : String} {p : Prop} [h : Decidable p] :
    Decidable (NamedBinder n p) := h

scoped instance (priority := high) {α : Type u} {l : List α} {p : α → Prop} [DecidablePred p]
    {n : String} : Decidable (∀ x, NamedBinder n (x ∈ l → p x)) :=
  inferInstanceAs (Decidable (∀ x, x ∈ l → p x))

def boundedRun {α : Type u} [Repr α] {β : α → Prop} [∀ x, Testable (β x)] (var : String)
    (cfg : Configuration) (min : Bool) : (l : List α) → Gen (TestResult (∀ x, x ∈ l → β x))
  | [] => pure (.success (PSum.inr (fun _ h => nomatch h)))
  | x :: xs => do
    match ← Testable.runProp (β x) cfg min with
    | .failure h msgs n =>
      pure (.failure (fun all => h (all x List.mem_cons_self)) (s!\"{var} := {repr x}\" :: msgs) n)
    | _ =>
      match ← boundedRun var cfg min xs with
      | .failure h msgs n =>
        pure (.failure (fun all => h (fun y hy => all y (List.mem_cons_of_mem _ hy))) msgs n)
      | _ => pure (.success (PSum.inl ()))

scoped instance (priority := high) {α : Type u} [Repr α] {l : List α} {β : α → Prop}
    [∀ x, Testable (β x)] {n n' : String} :
    Testable (NamedBinder n (∀ x, NamedBinder n' (x ∈ l → β x))) where
  run cfg min := boundedRun n cfg min l

def withSamples {α : Type} [Arbitrary α] (samples : List α) : Gen α :=
  Gen.frequency Arbitrary.arbitrary
    [(1, Arbitrary.arbitrary), (1, Gen.oneOfWithDefault Arbitrary.arbitrary (samples.map pure))]

end FormalRefute";

const COUNTEREXAMPLE_MARK: &str = "Found a counter-example!";

/// A Lean file that defines the code's model and states its properties.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeanSpec {
    /// What Lean reads, which is also what the cache keys digest: the specs it
    /// imports, then the spec, under one header of their imports. The spec as it
    /// was read when it imports no spec.
    pub source: String,
    /// The namespace that holds the definitions and the properties.
    pub namespace: String,
    /// The id of each `def <name> : Prop`, as `<namespace>.<name>`, in the spec's order.
    pub properties: Vec<String>,
    /// The functions whose doc comment names the code they describe, in the spec's order.
    pub compared: Vec<Compared>,
    /// The types the spec lists samples of, as `def <Type>.samples`, in name order.
    pub sampled: Vec<String>,
    /// The state machine the spec describes with `init` and `step`, when it has one.
    pub machine: Option<Machine>,
}

/// A state machine: an `init : <State>`, a `step`, and at least one invariant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Machine {
    /// Each `def <name> : <State> → Prop` or `def <name> (<s> : <State>) : Prop`, in the
    /// spec's order.
    pub invariants: Vec<String>,
    /// Each `inductive` and `structure` the spec defines, in the spec's order.
    pub types: Vec<String>,
}

impl Machine {
    /// What formal adds after the spec: `run`, and one property per invariant.
    fn definitions(&self, namespace: &str) -> String {
        let mut lines = vec![format!(
            "def _root_.{namespace}.run := List.foldl _root_.{namespace}.step _root_.{namespace}.init"
        )];
        lines.extend(self.invariants.iter().map(|invariant| {
            format!(
                "def _root_.{namespace}.{invariant}.{ALWAYS} : Prop := \
                 ∀ actions, _root_.{namespace}.{invariant} (_root_.{namespace}.run actions)"
            )
        }));
        lines.join("\n")
    }
}

/// A property the search found a counterexample to.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, serde::Serialize)]
pub struct Refutation {
    /// The property, as `<namespace>.<name>`.
    pub id: String,
    /// The value of each variable, as Plausible prints it.
    pub counterexample: Vec<String>,
    /// What does not hold for those values.
    pub issue: String,
}

/// What Lean said on the line of one search.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Answer {
    /// Lean said nothing, because the search never ran.
    Silent,
    /// The search ran and found no counterexample.
    Unrefuted,
    /// The search found a counterexample.
    Refuted(Refutation),
}

/// The file that searches properties for a counterexample, and the line of each search.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Search {
    /// The file, ready for Lean.
    pub lean_code: String,
    /// Each property, and the line that searches it.
    pub lines: Vec<(String, u32)>,
}

/// A function of the spec that names the code it describes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Compared {
    /// The function, as `<namespace>.<name>`.
    pub function: String,
    /// What the `code:` line of its doc comment says.
    pub code: String,
}

/// The inputs of a compared function, and the spec's answer to each.
#[derive(Clone, Debug, PartialEq, serde::Deserialize, serde::Serialize)]
pub struct Evaluated {
    /// The function, as `<namespace>.<name>`.
    pub function: String,
    /// What the `code:` line of its doc comment says.
    pub code: String,
    /// The inputs, as JSON.
    pub inputs: Vec<serde_json::Value>,
    /// The spec's answer to each input, in the same order.
    pub answers: Vec<serde_json::Value>,
}

/// The first input on which the code and the spec disagree.
#[derive(Clone, Debug, PartialEq)]
pub struct Difference {
    /// The function, as `<namespace>.<name>`.
    pub function: String,
    /// The input.
    pub input: serde_json::Value,
    /// What the spec answers.
    pub spec: serde_json::Value,
    /// What the code answers.
    pub code: serde_json::Value,
}

impl Evaluated {
    /// The first input whose answer from the code is not the spec's answer.
    #[must_use]
    pub fn first_difference(&self, code: &[serde_json::Value]) -> Option<Difference> {
        self.inputs
            .iter()
            .zip(&self.answers)
            .zip(code)
            .find(|((_, spec), code)| spec != code)
            .map(|((input, spec), code)| Difference {
                function: self.function.clone(),
                input: input.clone(),
                spec: spec.clone(),
                code: code.clone(),
            })
    }
}

/// A proof put after the spec it proves, ready for Lean.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Composed {
    /// The file to check.
    pub lean_code: String,
    offset: u32,
    proof_lines: u32,
}

impl Composed {
    /// The line of the proof that a line of the composed file came from.
    #[must_use]
    pub fn proof_line(&self, line: u32) -> Option<u32> {
        line.checked_sub(self.offset)
            .filter(|&proof_line| proof_line >= 1 && proof_line <= self.proof_lines)
    }
}

const IDENTIFIER: &str = r"[\p{L}_][\p{L}\p{N}_'!?]*";

fn pattern(cell: &'static OnceLock<Regex>, source: impl FnOnce() -> String) -> &'static Regex {
    cell.get_or_init(|| Regex::new(&source()).expect("the pattern is built from literals"))
}

fn namespace_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"^\s*namespace\s+({IDENTIFIER}(?:\.{IDENTIFIER})*)\s*$")
    })
}

fn end_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"^\s*end\s+({IDENTIFIER}(?:\.{IDENTIFIER})*)\s*$")
    })
}

fn identifier_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || format!(r"^{IDENTIFIER}$"))
}

fn prop_definition_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        r"\b(def|abbrev)\s+([^\s:]+)\s*:\s*Prop\s*:=".to_string()
    })
}

const DEFINITION: &str =
    r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial)\s+)*(?:def|abbrev)\s+";

fn definition_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"(?m)^[ \t]*{DEFINITION}({IDENTIFIER}(?:\.{IDENTIFIER})*)")
    })
}

fn doc_comment_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || r"(?s)/--(.*?)-/".to_string())
}

fn documented_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"\A\s*{DEFINITION}({IDENTIFIER}(?:\.{IDENTIFIER})*)")
    })
}

fn code_line_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        r"(?m)^[ \t]*code:[ \t]*(\S[^\n]*?)[ \t]*$".to_string()
    })
}

fn definitions<'a>(code: &'a str, blocks: &[(String, usize, usize)]) -> HashMap<&'a str, bool> {
    definition_pattern()
        .captures_iter(code)
        .filter_map(|found| {
            Some((
                found.get(1)?.as_str(),
                in_block(blocks, found.get(0)?.start()),
            ))
        })
        .collect()
}

fn in_block(blocks: &[(String, usize, usize)], at: usize) -> bool {
    blocks
        .iter()
        .any(|(_, start, end)| *start <= at && at < *end)
}

fn init_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"(?m)^[ \t]*{DEFINITION}init\s*:\s*({IDENTIFIER})\s*(?::=|where)")
    })
}

fn declared_type_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"(?m)^[ \t]*(?:inductive|structure)\s+({IDENTIFIER})")
    })
}

fn captured_in_block(
    pattern: &Regex,
    code: &str,
    blocks: &[(String, usize, usize)],
) -> Vec<String> {
    pattern
        .captures_iter(code)
        .filter(|found| {
            found
                .get(0)
                .is_some_and(|whole| in_block(blocks, whole.start()))
        })
        .map(|found| found[1].to_string())
        .collect()
}

fn machine(
    code: &str,
    blocks: &[(String, usize, usize)],
    defined: &HashMap<&str, bool>,
) -> Option<Machine> {
    if defined.get("step") != Some(&true) {
        return None;
    }
    let state = captured_in_block(init_pattern(), code, blocks)
        .into_iter()
        .next()?;
    let state = regex::escape(&state);
    let invariant = Regex::new(&format!(
        r"(?m)^[ \t]*{DEFINITION}({IDENTIFIER})\s*(?::\s*{state}\s*→|\(\s*{IDENTIFIER}\s*:\s*{state}\s*\)\s*:)\s*Prop\s*:="
    ))
    .expect("the pattern is built from literals");
    let invariants = captured_in_block(&invariant, code, blocks);
    if invariants.is_empty() {
        return None;
    }
    Some(Machine {
        invariants,
        types: captured_in_block(declared_type_pattern(), code, blocks),
    })
}

fn sampled_types(defined: &HashMap<&str, bool>) -> Vec<String> {
    let mut types: Vec<String> = defined
        .iter()
        .filter(|(_, inside)| **inside)
        .filter_map(|(name, _)| name.strip_suffix(".samples"))
        .filter(|name| identifier_pattern().is_match(name))
        .map(ToString::to_string)
        .collect();
    types.sort();
    types
}

fn compared_functions(
    path: &Path,
    text: &str,
    namespace: &str,
    defined: &HashMap<&str, bool>,
) -> Result<Vec<Compared>, SpecError> {
    let mut compared = Vec::new();
    for found in doc_comment_pattern().captures_iter(text) {
        let Some(code_line) = code_line_pattern().captures(&found[1]) else {
            continue;
        };
        let after = found.get(0).map_or("", |whole| &text[whole.end()..]);
        let name = documented_pattern()
            .captures(after)
            .and_then(|documented| documented.get(1))
            .map(|name| name.as_str());
        let name = match name.map(|name| (name, defined.get(name))) {
            Some((_, None)) => continue,
            Some((name, Some(true))) => name,
            _ => {
                return Err(SpecError::UncomparableCode {
                    path: path.to_path_buf(),
                    line: format!("code: {}", &code_line[1]),
                });
            }
        };
        let function = format!("{namespace}.{name}");
        if defined.get(format!("{name}.inputs").as_str()) != Some(&true) {
            return Err(SpecError::NoInputs {
                path: path.to_path_buf(),
                function,
            });
        }
        compared.push(Compared {
            function,
            code: code_line[1].to_string(),
        });
    }
    Ok(compared)
}

const SPEC_IMPORT: &str = "Spec.";

fn imported_specs(path: &Path, text: &str) -> Result<Vec<String>, SpecError> {
    let root = path.parent().unwrap_or(path);
    let mut read = Vec::new();
    visit(root, path, text, &mut vec![path.to_path_buf()], &mut read)?;
    Ok(read.into_iter().map(|(_, text)| text).collect())
}

fn visit(
    root: &Path,
    path: &Path,
    text: &str,
    importing: &mut Vec<PathBuf>,
    read: &mut Vec<(PathBuf, String)>,
) -> Result<(), SpecError> {
    for import in imports(text.trim_start_matches('\u{feff}')) {
        let Some(name) = import.module.strip_prefix(SPEC_IMPORT) else {
            continue;
        };
        let imported = root.join(format!("{}.lean", name.replace('.', "/")));
        if let Some(start) = importing.iter().position(|seen| *seen == imported) {
            let chain: Vec<String> = importing[start..]
                .iter()
                .chain(std::iter::once(&imported))
                .map(|step| step.display().to_string())
                .collect();
            return Err(SpecError::ImportCycle {
                chain: chain.join(" → "),
            });
        }
        if read.iter().any(|(done, _)| *done == imported) {
            continue;
        }
        let imported_text = fs::read_to_string(&imported).map_err(|_| SpecError::NoSuchImport {
            spec: path.to_path_buf(),
            import: import.module.clone(),
            path: imported.clone(),
        })?;
        if let Some(found) = runs_code(&imported_text) {
            return Err(SpecError::RunsCode {
                path: imported,
                found,
            });
        }
        importing.push(imported.clone());
        visit(root, &imported, &imported_text, importing, read)?;
        importing.pop();
        read.push((imported, imported_text));
    }
    Ok(())
}

fn source(text: String, imported: &[String]) -> String {
    if imported.is_empty() {
        return text;
    }
    let files: Vec<&str> = imported
        .iter()
        .map(String::as_str)
        .chain(std::iter::once(text.as_str()))
        .map(|file| file.trim_start_matches('\u{feff}'))
        .collect();
    let modules: Vec<String> = files
        .iter()
        .flat_map(|file| imports(file))
        .map(|import| import.module)
        .filter(|module| !module.starts_with(SPEC_IMPORT))
        .collect();
    let mut lines = import_lines(modules.iter().map(String::as_str));
    lines.extend(files.iter().map(|file| blanked(file, &imports(file))));
    format!("{}\n", lines.join("\n"))
}

fn import_lines<'a>(modules: impl Iterator<Item = &'a str>) -> Vec<String> {
    let mut lines: Vec<String> = Vec::new();
    for module in modules {
        let line = format!("import {module}");
        if !lines.contains(&line) {
            lines.push(line);
        }
    }
    lines
}

fn search_of(id: &str) -> String {
    format!("open FormalRefute in example : _root_.{id} := by unfold _root_.{id}; plausible")
}

fn evaluation_of(function: &str) -> String {
    format!(
        "open FormalCompare in\n#eval IO.println (\"{COMPARE_MARK} {function} \" ++ \
         (Lean.toJson ((_root_.{function}.inputs).map fun input => (input, _root_.{function} input))).compress)"
    )
}

fn blanked(code: &str, imports: &[Import]) -> String {
    let mut kept = String::with_capacity(code.len());
    let mut from = 0;
    for import in imports {
        kept.push_str(&code[from..import.start]);
        kept.extend(
            code[import.start..import.end]
                .chars()
                .map(|c| if c == '\n' { '\n' } else { ' ' }),
        );
        from = import.end;
    }
    kept.push_str(&code[from..]);
    kept
}

impl LeanSpec {
    /// Read the spec at an absolute path.
    ///
    /// # Errors
    ///
    /// [`SpecError`] when the path is relative or names nothing, or when the
    /// spec can run code, opens no namespace or more than one, states no
    /// property, or states one that formal cannot register.
    pub fn load(path: &str) -> Result<Self, SpecError> {
        let path = expanduser(path);
        require_absolute(&path, "spec")?;
        let text = fs::read_to_string(&path).map_err(|_| SpecError::NoSuchFile(path.clone()))?;
        Self::parse(&path, text)
    }

    fn parse(path: &Path, text: String) -> Result<Self, SpecError> {
        if let Some(found) = runs_code(&text) {
            return Err(SpecError::RunsCode {
                path: path.to_path_buf(),
                found,
            });
        }
        let code = without_comments(text.trim_start_matches('\u{feff}'));
        let mut namespaces: Vec<String> = Vec::new();
        let mut blocks: Vec<(String, usize, usize)> = Vec::new();
        let mut open: Option<(String, usize)> = None;
        let mut offset = 0;
        for line in code.split_inclusive('\n') {
            if let Some(found) = namespace_pattern().captures(line.trim_end()) {
                let namespace = found[1].to_string();
                if !namespaces.contains(&namespace) {
                    namespaces.push(namespace.clone());
                }
                open = Some((namespace, offset));
            } else if let Some(found) = end_pattern().captures(line.trim_end())
                && let Some((namespace, start)) = open.take_if(|(name, _)| *name == found[1])
            {
                blocks.push((namespace, start, offset));
            }
            offset += line.len();
        }
        if let Some((namespace, start)) = open {
            blocks.push((namespace, start, code.len()));
        }

        let mut properties = Vec::new();
        for found in prop_definition_pattern().captures_iter(&code) {
            let whole = found.get(0).map_or(0..0, |whole| whole.range());
            let line_start = code[..whole.start].rfind('\n').map_or(0, |index| index + 1);
            let block = blocks
                .iter()
                .find(|(_, start, end)| *start <= whole.start && whole.start < *end);
            let registrable = &found[1] == "def"
                && code[line_start..whole.start].trim().is_empty()
                && identifier_pattern().is_match(&found[2]);
            match block {
                Some((namespace, _, _)) if registrable => {
                    properties.push(format!("{namespace}.{}", &found[2]));
                }
                _ => {
                    let line_end = code[whole.end..]
                        .find('\n')
                        .map_or(code.len(), |index| whole.end + index);
                    return Err(SpecError::UnregisteredProperty {
                        path: path.to_path_buf(),
                        line: code[line_start..line_end]
                            .split_whitespace()
                            .collect::<Vec<_>>()
                            .join(" "),
                    });
                }
            }
        }
        let namespace = match namespaces.as_slice() {
            [] => return Err(SpecError::NoNamespace(path.to_path_buf())),
            [namespace] => namespace.clone(),
            _ => {
                return Err(SpecError::Namespaces {
                    path: path.to_path_buf(),
                    found: namespaces,
                });
            }
        };
        let defined = definitions(&code, &blocks);
        let machine = machine(&code, &blocks, &defined);
        if let Some(machine) = &machine {
            if defined.contains_key("run") {
                return Err(SpecError::MachineRun(path.to_path_buf()));
            }
            properties.extend(
                machine
                    .invariants
                    .iter()
                    .map(|invariant| format!("{namespace}.{invariant}.{ALWAYS}")),
            );
        }
        if properties.is_empty() {
            return Err(SpecError::NoLeanProperties(path.to_path_buf()));
        }
        let compared = compared_functions(path, &text, &namespace, &defined)?;
        let sampled = sampled_types(&defined);
        let imported = imported_specs(path, &text)?;
        let mut source = source(text, &imported);
        if let Some(machine) = &machine {
            source.push('\n');
            source.push_str(&machine.definitions(&namespace));
            source.push('\n');
        }
        Ok(Self {
            source,
            namespace,
            properties,
            compared,
            sampled,
            machine,
        })
    }

    /// The properties as a session holds them.
    #[must_use]
    pub fn property_specs(&self) -> Vec<PropertySpec> {
        self.properties
            .iter()
            .map(|id| PropertySpec {
                id: id.clone(),
                kind: "spec".to_string(),
                ..PropertySpec::default()
            })
            .collect()
    }

    /// The cache key of a property, which covers the whole spec.
    #[must_use]
    pub fn key(&self, id: &str) -> String {
        lean_spec_key(&self.source, id)
    }

    /// The cache key of the spec's answers for a compared function.
    #[must_use]
    pub fn answers_key(&self, function: &str) -> String {
        lean_spec_answers_key(&self.source, ENCODING, &evaluation_of(function))
    }

    /// The file that prints the inputs of each function in `functions`, and the spec's answers.
    ///
    /// Each function prints one line: [`COMPARE_MARK`], the function, and a JSON
    /// list of `[input, answer]` pairs.
    #[must_use]
    pub fn evaluation(&self, functions: &[&str]) -> String {
        let spec = self.source.trim_start_matches('\u{feff}');
        let spec_imports = imports(spec);
        let mut lines = import_lines(
            std::iter::once(EVALUATION_IMPORT)
                .chain(spec_imports.iter().map(|import| import.module.as_str())),
        );
        lines.push(blanked(spec, &spec_imports));
        lines.push(ENCODING.to_string());
        lines.extend(functions.iter().map(|function| evaluation_of(function)));
        format!("{}\n", lines.join("\n"))
    }

    /// The cache key of the search for a counterexample to the property `id`.
    #[must_use]
    pub fn search_key(&self, id: &str) -> String {
        let helpers = std::iter::once(SEARCH_HELPERS.to_string())
            .chain(self.derived())
            .collect::<Vec<_>>()
            .join("\n");
        lean_spec_search_key(&self.source, &helpers, &self.search_line(id))
    }

    fn search_line(&self, id: &str) -> String {
        let invariant = id
            .strip_prefix(&format!("{}.", self.namespace))
            .and_then(|name| name.strip_suffix(&format!(".{ALWAYS}")))
            .filter(|name| {
                self.machine.as_ref().is_some_and(|machine| {
                    machine.invariants.iter().any(|invariant| invariant == name)
                })
            });
        match invariant {
            Some(invariant) => format!(
                "open FormalRefute in example : _root_.{id} := by \
                 unfold _root_.{id} _root_.{}.{invariant}; plausible",
                self.namespace
            ),
            None => search_of(id),
        }
    }

    fn derived(&self) -> Vec<String> {
        let namespace = &self.namespace;
        self.machine
            .iter()
            .flat_map(|machine| &machine.types)
            .flat_map(|derived| {
                ["Repr", "Plausible.Shrinkable", "Plausible.Arbitrary"]
                    .map(|class| format!("deriving instance {class} for {namespace}.{derived}"))
            })
            .collect()
    }

    /// The file that searches each property in `ids` for a counterexample.
    ///
    /// The values of a type the spec lists samples of are drawn half from
    /// those samples. Each search is one line, and Lean answers it on that line.
    #[must_use]
    pub fn search(&self, ids: &[&str]) -> Search {
        let spec = self.source.trim_start_matches('\u{feff}');
        let spec_imports = imports(spec);
        let mut lines = import_lines(
            std::iter::once(SEARCH_IMPORT)
                .chain(spec_imports.iter().map(|import| import.module.as_str())),
        );
        lines.extend(blanked(spec, &spec_imports).split('\n').map(str::to_string));
        lines.extend(SEARCH_HELPERS.split('\n').map(str::to_string));
        let namespace = &self.namespace;
        lines.extend(self.derived());
        lines.extend(self.sampled.iter().map(|sampled| {
            format!(
                "open {namespace} in instance (priority := high) : Plausible.Arbitrary {sampled} := \
                 ⟨FormalRefute.withSamples {namespace}.{sampled}.samples⟩"
            )
        }));
        let mut searched = Vec::new();
        for id in ids {
            lines.push(self.search_line(id));
            searched.push((
                (*id).to_string(),
                u32::try_from(lines.len()).unwrap_or(u32::MAX),
            ));
        }
        Search {
            lean_code: format!("{}\n", lines.join("\n")),
            lines: searched,
        }
    }

    /// The file that checks `proof` against the property `id`.
    ///
    /// The imports of the spec and the proof come first, then the spec and a
    /// line that requires the spec to define `id`. The proof follows with its
    /// imports blanked, so that its lines keep their numbers. The last line
    /// calls a command defined before the proof, which requires `<id>.holds`
    /// to state the spec's own property.
    #[must_use]
    pub fn compose(&self, id: &str, proof: &str) -> Composed {
        let spec = self.source.trim_start_matches('\u{feff}');
        let proof = proof.trim_start_matches('\u{feff}');
        let spec_imports = imports(spec);
        let proof_imports = imports(proof);

        let mut lines = import_lines(
            spec_imports
                .iter()
                .chain(&proof_imports)
                .map(|import| import.module.as_str()),
        );
        lines.extend(blanked(spec, &spec_imports).split('\n').map(str::to_string));
        lines.push(format!("#check _root_.{id}"));
        let offset = u32::try_from(lines.len()).unwrap_or(u32::MAX);
        let body = blanked(proof, &proof_imports);
        lines.extend(body.split('\n').map(str::to_string));
        lines.push(format!("{HOLDS_COMMAND} \"{id}\""));
        Composed {
            lean_code: format!("{}\n", lines.join("\n")),
            offset,
            proof_lines: u32::try_from(body.split('\n').count()).unwrap_or(u32::MAX),
        }
    }
}

/// What Lean said on each line of `search`, one answer per line, in order.
#[must_use]
pub fn read_search(search: &Search, said: &[(u32, String)]) -> Vec<Answer> {
    search
        .lines
        .iter()
        .map(|(id, line)| {
            let mut on_line = said.iter().filter(|(at, _)| at == line).peekable();
            if on_line.peek().is_none() {
                return Answer::Silent;
            }
            on_line
                .find_map(|(_, data)| refutation(id, data))
                .map_or(Answer::Unrefuted, Answer::Refuted)
        })
        .collect()
}

fn refutation(id: &str, data: &str) -> Option<Refutation> {
    let (_, found) = data.split_once(COUNTEREXAMPLE_MARK)?;
    let mut entries: Vec<String> = Vec::new();
    for line in found.split('\n').filter(|line| !line.is_empty()) {
        if line.starts_with('(') || line.starts_with('-') {
            break;
        }
        match entries.last_mut() {
            Some(entry) if line.starts_with(' ') => {
                entry.push('\n');
                entry.push_str(line);
            }
            _ => entries.push(line.to_string()),
        }
    }
    let issue = entries
        .iter()
        .find_map(|entry| entry.strip_prefix("issue: "))?;
    Some(Refutation {
        id: id.to_string(),
        counterexample: entries
            .iter()
            .filter(|entry| !entry.starts_with("issue: ") && !entry.starts_with("guard:"))
            .cloned()
            .collect(),
        issue: issue.to_string(),
    })
}

/// The answers the evaluation of `compared` printed, one per function.
///
/// # Errors
///
/// What is wrong, when a function printed no line, more than one, or a line
/// that is not a JSON list of `[input, answer]` pairs.
pub fn read_evaluation(compared: &[&Compared], printed: &[&str]) -> Result<Vec<Evaluated>, String> {
    compared
        .iter()
        .map(|Compared { function, code }| {
            let mark = format!("{COMPARE_MARK} {function} ");
            let lines: Vec<&str> = printed
                .iter()
                .filter_map(|line| line.strip_prefix(&mark))
                .collect();
            let [line] = lines.as_slice() else {
                return Err(format!(
                    "the evaluation printed {} answers for {function}, not one",
                    lines.len()
                ));
            };
            let pairs: Vec<(serde_json::Value, serde_json::Value)> =
                serde_json::from_str(line.trim_end()).map_err(|e| {
                    format!("the evaluation of {function} printed something else than pairs: {e}")
                })?;
            let (inputs, answers) = pairs.into_iter().unzip();
            Ok(Evaluated {
                function: function.clone(),
                code: code.clone(),
                inputs,
                answers,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use tempfile::TempDir;

    use super::*;

    const DEMO: &str = include_str!("../../../tests/fixtures/lean_spec/Demo.lean");

    fn parse(text: &str) -> Result<LeanSpec, SpecError> {
        LeanSpec::parse(&PathBuf::from("/specs/Demo.lean"), text.to_string())
    }

    fn with(extra: &str) -> Result<LeanSpec, SpecError> {
        parse(&DEMO.replace("end Demo", &format!("{extra}\n\nend Demo")))
    }

    fn demo() -> LeanSpec {
        parse(DEMO).expect("the demo spec parses")
    }

    #[test]
    fn only_the_props_are_properties_and_they_keep_their_order() {
        assert_eq!(demo().properties, ["Demo.double_even", "Demo.double_mono"]);
    }

    #[test]
    fn a_property_may_be_indented_or_follow_its_doc_on_the_line() {
        let spec = with("  def indented : Prop := True\n/-- why -/ def documented : Prop := True")
            .expect("it parses");
        assert_eq!(
            spec.properties,
            [
                "Demo.double_even",
                "Demo.double_mono",
                "Demo.indented",
                "Demo.documented"
            ]
        );
    }

    #[test]
    fn a_name_takes_the_identifier_characters_of_lean() {
        let spec = parse(&DEMO.replace("double_mono", "double_mono'")).expect("it parses");
        assert_eq!(spec.properties, ["Demo.double_even", "Demo.double_mono'"]);
    }

    #[test]
    fn a_definition_whose_type_only_starts_with_prop_is_not_a_property() {
        let spec = with("def lift : Prop → Prop := id\ndef pair : Prop × Prop := (True, True)")
            .expect("it parses");
        assert_eq!(spec.properties, ["Demo.double_even", "Demo.double_mono"]);
    }

    #[test]
    fn a_property_in_a_comment_is_not_one() {
        let spec = with(
            "/-\ndef gone : Prop := True\nnamespace Model, below.\n-/\n-- def also_gone : Prop := True",
        )
        .expect("it parses");
        assert_eq!(spec.namespace, "Demo");
        assert_eq!(spec.properties, ["Demo.double_even", "Demo.double_mono"]);
    }

    #[test]
    fn a_property_formal_cannot_register_is_refused() {
        for written in [
            "@[simp] def tagged : Prop := True",
            "protected def guarded : Prop := True",
        ] {
            let refused = with(written);
            assert!(
                matches!(refused, Err(SpecError::UnregisteredProperty { .. })),
                "{written}: {refused:?}"
            );
        }
    }

    #[test]
    fn a_property_outside_the_namespace_is_refused() {
        let refused = parse(&format!(
            "{DEMO}\ndef outside : Prop := False\n\nnamespace Demo\n\ndef inside : Prop := True\n\nend Demo\n"
        ));
        assert!(
            matches!(refused, Err(SpecError::UnregisteredProperty { ref line, .. }) if line.contains("outside")),
            "{refused:?}"
        );
    }

    #[test]
    fn a_spec_with_two_namespaces_is_refused() {
        let refused = parse(&format!(
            "{DEMO}\nnamespace Other\ndef p : Prop := True\nend Other\n"
        ));
        assert!(
            matches!(refused, Err(SpecError::Namespaces { .. })),
            "{refused:?}"
        );
    }

    #[test]
    fn a_spec_that_runs_code_is_refused() {
        let refused = parse(&format!("{DEMO}\n#eval 1\n"));
        assert!(
            matches!(refused, Err(SpecError::RunsCode { .. })),
            "{refused:?}"
        );
    }

    #[test]
    fn a_spec_without_a_namespace_or_a_property_is_refused() {
        assert!(matches!(
            parse("def p : Prop := True\n"),
            Err(SpecError::UnregisteredProperty { .. })
        ));
        assert!(matches!(
            parse("def n : Nat := 1\n"),
            Err(SpecError::NoNamespace(_))
        ));
        assert!(matches!(
            parse("namespace E\ndef n : Nat := 1\nend E\n"),
            Err(SpecError::NoLeanProperties(_))
        ));
        assert!(matches!(
            LeanSpec::load("Relative.lean"),
            Err(SpecError::NotAbsolute { .. })
        ));
    }

    #[test]
    fn any_edit_to_the_spec_moves_every_key() {
        let original = demo();
        for edited in [
            DEMO.replace("n + n", "2 * n"),
            DEMO.replace("n + n", "n + n   "),
        ] {
            let edited = parse(&edited).expect("it parses");
            for id in &original.properties {
                assert_ne!(original.key(id), edited.key(id));
            }
        }
        assert_ne!(
            original.key("Demo.double_even"),
            original.key("Demo.double_mono")
        );
    }

    #[test]
    fn no_inline_property_shares_the_key_of_a_spec_property() {
        let spec = demo();
        let inline = PropertySpec {
            function_code: spec.source.clone(),
            kind: "spec".to_string(),
            formal: "Demo.double_even".to_string(),
            ..PropertySpec::default()
        };
        assert_ne!(inline.cache_key(), spec.key("Demo.double_even"));
    }

    #[test]
    fn the_composed_file_imports_once_and_keeps_the_proof_lines() {
        let proof = "/- Copyright\nimport Fake -/\nimport Mathlib\nimport Mathlib.Tactic\n\nnamespace Demo\ntheorem double_even.holds : double_even := by\n  omega\nend Demo";
        let composed = demo().compose("Demo.double_even", proof);
        let lines: Vec<&str> = composed.lean_code.split('\n').collect();
        assert_eq!(lines[..2], ["import Mathlib", "import Mathlib.Tactic"]);
        assert_eq!(
            lines
                .iter()
                .filter(|line| line.starts_with("import "))
                .count(),
            3
        );
        assert_eq!(
            lines
                .iter()
                .filter(|line| **line == "import Mathlib")
                .count(),
            1
        );
        let omega = lines
            .iter()
            .position(|line| *line == "  omega")
            .expect("the proof is in");
        assert_eq!(
            composed.proof_line(u32::try_from(omega + 1).expect("it fits")),
            Some(8)
        );
        assert!(
            composed
                .lean_code
                .contains("end Demo\n\n#check _root_.Demo.double_even\n/- Copyright")
        );
        assert!(
            composed
                .lean_code
                .ends_with("\n#formal_holds \"Demo.double_even\"\n")
        );
    }

    #[test]
    fn only_the_module_name_of_an_import_moves_before_the_spec() {
        let composed = demo().compose(
            "Demo.double_even",
            "/- c\n-/ import Mathlib /- open -/\nimport Mathlib.Tactic infixl:65 \" ++ \" => fun _ b => b\ntheorem t : True := trivial",
        );
        let spec_at = composed
            .lean_code
            .find("namespace Demo")
            .expect("the spec is in");
        assert_eq!(
            &composed.lean_code[..spec_at],
            "import Mathlib\nimport Mathlib.Tactic\n"
        );
        let body: Vec<&str> = composed.lean_code.split('\n').collect();
        assert!(body.contains(&format!("-/{}/- open -/", " ".repeat(16)).as_str()));
        assert!(
            body.contains(
                &format!("{}infixl:65 \" ++ \" => fun _ b => b", " ".repeat(22)).as_str()
            )
        );
    }

    #[test]
    fn a_byte_order_mark_does_not_hide_the_imports() {
        let composed = demo().compose(
            "Demo.double_even",
            "\u{feff}import Mathlib\ntheorem t : True := trivial",
        );
        assert!(
            composed
                .lean_code
                .starts_with("import Mathlib\nnamespace Demo")
        );
        let spec = parse(&format!("\u{feff}{DEMO}")).expect("it parses");
        assert_eq!(spec.namespace, "Demo");
    }

    #[test]
    fn a_property_may_break_across_lines_and_an_abbreviation_is_refused() {
        let spec =
            with("def split :\n  Prop := True\ndef late : Prop\n  := True").expect("it parses");
        assert_eq!(
            spec.properties,
            [
                "Demo.double_even",
                "Demo.double_mono",
                "Demo.split",
                "Demo.late"
            ]
        );
        let refused = with("abbrev shorthand : Prop := True");
        assert!(
            matches!(refused, Err(SpecError::UnregisteredProperty { .. })),
            "{refused:?}"
        );
    }

    const COMPARED: &str = "/-- Doubles.\n\n  code: src/double.rs double\n-/\ndef twice (n : Nat) : Nat := n + n\n\ndef twice.inputs : List Nat := [0, 1, 2]";

    #[test]
    fn a_code_line_in_a_doc_comment_names_the_code_of_a_function() {
        let spec = with(&format!(
            "{COMPARED}\n/-- code: src/half.rs half -/ def half (n : Nat) : Nat := n / 2\ndef half.inputs : List Nat := [4]"
        ))
        .expect("it parses");
        assert_eq!(
            spec.compared,
            [
                Compared {
                    function: "Demo.twice".to_string(),
                    code: "src/double.rs double".to_string(),
                },
                Compared {
                    function: "Demo.half".to_string(),
                    code: "src/half.rs half".to_string(),
                },
            ]
        );
        assert_eq!(demo().compared, []);
    }

    #[test]
    fn a_doc_comment_without_a_code_line_or_on_a_dead_definition_compares_nothing() {
        let spec = with(
            "/-- What double does. -/\ndef plain (n : Nat) : Nat := n\n/-\n/-- code: src/gone.rs gone -/\ndef gone (n : Nat) : Nat := n\n-/",
        )
        .expect("it parses");
        assert_eq!(spec.compared, []);
    }

    #[test]
    fn a_code_line_names_only_the_function_its_doc_comment_sits_on() {
        let spec = with(
            "/-- code: src/a.rs a -/\n@[simp] def a (n : Nat) : Nat := n\ndef a.inputs : List Nat := [0]\n/-- Helper. -/\ndef b (n : Nat) : Nat := n",
        )
        .expect("it parses");
        assert_eq!(
            spec.compared,
            [Compared {
                function: "Demo.a".to_string(),
                code: "src/a.rs a".to_string(),
            }]
        );
    }

    #[test]
    fn a_code_line_on_a_dotted_function_names_that_function() {
        let spec = with(
            "def f (n : Nat) : Nat := n\n/-- code: src/f.rs go -/\ndef f.go (n : Nat) : Nat := n\ndef f.go.inputs : List Nat := [0]",
        )
        .expect("it parses");
        assert_eq!(
            spec.compared,
            [Compared {
                function: "Demo.f.go".to_string(),
                code: "src/f.rs go".to_string(),
            }]
        );
    }

    #[test]
    fn a_compared_function_and_its_inputs_may_carry_attributes_and_modifiers() {
        let spec = with(
            "/-- code: src/f.rs f -/\npartial def f (n : Nat) : Nat := n\n@[reducible] abbrev f.inputs : List Nat := [0]",
        )
        .expect("it parses");
        assert_eq!(
            spec.compared,
            [Compared {
                function: "Demo.f".to_string(),
                code: "src/f.rs f".to_string(),
            }]
        );
    }

    #[test]
    fn a_code_line_on_no_function_of_the_namespace_is_refused() {
        let loose = with("/-- code: src/x.rs x -/\ntheorem x : True := trivial");
        assert!(
            matches!(loose, Err(SpecError::UncomparableCode { ref line, .. }) if line == "code: src/x.rs x"),
            "{loose:?}"
        );
        let outside = parse(&format!(
            "/-- code: src/f.rs f -/\ndef f (n : Nat) : Nat := n\ndef f.inputs : List Nat := [0]\n{DEMO}"
        ));
        assert!(
            matches!(outside, Err(SpecError::UncomparableCode { ref line, .. }) if line == "code: src/f.rs f"),
            "{outside:?}"
        );
    }

    #[test]
    fn a_function_that_names_its_code_without_inputs_is_refused() {
        let refused = with(&COMPARED.replace("def twice.inputs", "def twice_inputs"));
        assert!(
            matches!(refused, Err(SpecError::NoInputs { ref function, .. }) if function == "Demo.twice"),
            "{refused:?}"
        );
    }

    #[test]
    fn the_evaluation_prints_each_function_after_the_spec() {
        let spec = with(COMPARED).expect("it parses");
        let evaluation = spec.evaluation(&["Demo.twice"]);
        assert!(evaluation.starts_with("import Lean.Data.Json\nnamespace Demo"));
        assert!(evaluation.contains("end FormalCompare\nopen FormalCompare in\n#eval"));
        assert!(evaluation.ends_with(
            "(Lean.toJson ((_root_.Demo.twice.inputs).map fun input => (input, _root_.Demo.twice input))).compress)\n"
        ));
    }

    fn twice() -> Compared {
        Compared {
            function: "Demo.twice".to_string(),
            code: "src/double.rs double".to_string(),
        }
    }

    #[test]
    fn the_evaluation_is_read_back_as_inputs_and_answers() {
        let read = read_evaluation(
            &[&twice()],
            &[
                "formal-audit 1 []",
                "formal-compare Demo.twice [[0,0],[1,2]]\n",
            ],
        )
        .expect("it reads");
        assert_eq!(
            read,
            [Evaluated {
                function: "Demo.twice".to_string(),
                code: "src/double.rs double".to_string(),
                inputs: vec![0.into(), 1.into()],
                answers: vec![0.into(), 2.into()],
            }]
        );
    }

    #[test]
    fn the_first_input_where_the_answers_part_is_the_difference() {
        let evaluated = Evaluated {
            function: "Demo.twice".to_string(),
            code: "src/double.rs double".to_string(),
            inputs: vec![0.into(), 1.into(), 2.into()],
            answers: vec![0.into(), 2.into(), 4.into()],
        };
        assert_eq!(
            evaluated.first_difference(&[0.into(), 2.into(), 4.into()]),
            None
        );
        assert_eq!(
            evaluated.first_difference(&[0.into(), 3.into(), 5.into()]),
            Some(Difference {
                function: "Demo.twice".to_string(),
                input: 1.into(),
                spec: 2.into(),
                code: 3.into(),
            })
        );
        assert!(
            evaluated
                .first_difference(&[0.into(), "2".into(), 4.into()])
                .is_some()
        );
    }

    #[test]
    fn an_evaluation_that_printed_no_line_two_or_no_pairs_is_refused() {
        for printed in [
            vec![],
            vec![
                "formal-compare Demo.twice []",
                "formal-compare Demo.twice []",
            ],
            vec!["formal-compare Demo.twice [1, 2]"],
        ] {
            assert!(
                read_evaluation(&[&twice()], &printed).is_err(),
                "{printed:?}"
            );
        }
    }

    #[test]
    fn a_type_with_samples_inside_the_namespace_is_sampled() {
        let spec = with("def Char.samples : List Char := ['a']\ndef Nat.samples : List Nat := [0]")
            .expect("it parses");
        assert_eq!(spec.sampled, ["Char", "Nat"]);
        assert_eq!(
            parse(&format!("def Char.samples : List Char := ['a']\n{DEMO}"))
                .expect("it parses")
                .sampled,
            Vec::<String>::new()
        );
    }

    #[test]
    fn the_search_draws_from_the_samples_and_gives_each_property_its_own_line() {
        let spec = with("def Char.samples : List Char := ['a']").expect("it parses");
        let search = spec.search(&["Demo.double_even", "Demo.double_mono"]);
        let lines: Vec<&str> = search.lean_code.split('\n').collect();
        assert_eq!(lines[0], "import Plausible");
        assert!(search.lean_code.contains(
            "open Demo in instance (priority := high) : Plausible.Arbitrary Char := ⟨FormalRefute.withSamples Demo.Char.samples⟩"
        ));
        for (id, line) in &search.lines {
            let at = usize::try_from(*line).expect("it fits") - 1;
            assert_eq!(
                lines[at],
                format!(
                    "open FormalRefute in example : _root_.{id} := by unfold _root_.{id}; plausible"
                )
            );
        }
    }

    const SEARCHED: &str = "namespace Demo\n\ndef double (n : Nat) : Nat := n + n\n\ndef double_odd : Prop := ∀ n, double n % 2 = 1\n\ndef double_mono : Prop := ∀ a b, a ≤ b → double a ≤ double b\n\ndef Char.samples : List Char := ['\\u2028']\n\ndef space_free : Prop := ∀ s : List Char, ∀ c ∈ s, c.toNat < 128\n\nend Demo\n";

    #[test]
    fn what_lean_said_on_a_search_line_is_read_as_a_refutation_or_as_nothing_found() {
        let spec = parse(SEARCHED).expect("it parses");
        let search = spec.search(&["Demo.double_odd", "Demo.double_mono", "Demo.space_free"]);
        let line = |at: usize| search.lines[at].1;
        let said = [
            (
                line(0),
                "\n===================\nFound a counter-example!\nn := 0\nissue: 0 = 1 does not hold\n(0 shrinks)\n-------------------".to_string(),
            ),
            (line(1), "Unable to find a counter-example".to_string()),
            (line(1), "declaration uses `sorry`".to_string()),
            (
                line(2),
                "\n===================\nFound a counter-example!\ns := ['\u{2028}']\nc := '\u{2028}'\nissue: 8232 < 128 does not hold\n(5 shrinks)\n-------------------".to_string(),
            ),
        ];
        let refutation = |id: &str, counterexample: &[&str], issue: &str| {
            Answer::Refuted(Refutation {
                id: id.to_string(),
                counterexample: counterexample.iter().map(ToString::to_string).collect(),
                issue: issue.to_string(),
            })
        };
        assert_eq!(
            read_search(&search, &said),
            [
                refutation("Demo.double_odd", &["n := 0"], "0 = 1 does not hold"),
                Answer::Unrefuted,
                refutation(
                    "Demo.space_free",
                    &["s := ['\u{2028}']", "c := '\u{2028}'"],
                    "8232 < 128 does not hold"
                ),
            ]
        );
        assert_eq!(
            read_search(&search, &said[1..3]),
            [Answer::Silent, Answer::Unrefuted, Answer::Silent]
        );
    }

    #[test]
    fn a_value_lean_wraps_over_several_lines_stays_one_value() {
        let spec = demo();
        let search = spec.search(&["Demo.double_even"]);
        let line = search.lines[0].1;
        let found = "\n===================\nFound a counter-example!\ns := [0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0]\nissue: 45 < 45 does not hold\n(211 shrinks)\n-------------------";
        let read = read_search(&search, &[(line, found.to_string())]);
        let [Answer::Refuted(refutation)] = read.as_slice() else {
            panic!("one refutation, got {read:?}");
        };
        assert_eq!(
            refutation.counterexample,
            [
                "s := [0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0]"
            ]
        );
        assert_eq!(refutation.issue, "45 < 45 does not hold");
    }

    const COUNTER: &str = "namespace Counter\n\ninductive Action where\n  | inc\n  | reset\n\nstructure State where\n  count : Nat\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .inc => ⟨s.count + 1⟩\n  | .reset => ⟨0⟩\n\ndef count_below_three : State → Prop := fun s => s.count < 3\n\ndef init_is_zero : Prop := init.count = 0\n\nend Counter\n";

    #[test]
    fn an_init_and_a_step_make_a_machine_and_each_invariant_a_property() {
        let spec = parse(COUNTER).expect("it parses");
        assert_eq!(
            spec.machine,
            Some(Machine {
                invariants: vec!["count_below_three".to_string()],
                types: vec!["Action".to_string(), "State".to_string()],
            })
        );
        assert_eq!(
            spec.properties,
            ["Counter.init_is_zero", "Counter.count_below_three.always"]
        );
        assert!(
            spec.source.ends_with(
                "def _root_.Counter.run := List.foldl _root_.Counter.step _root_.Counter.init\ndef _root_.Counter.count_below_three.always : Prop := ∀ actions, _root_.Counter.count_below_three (_root_.Counter.run actions)\n"
            ),
            "{}",
            spec.source
        );
        assert_eq!(demo().machine, None);
        assert!(!demo().source.contains("def run"));
    }

    #[test]
    fn a_machine_whose_invariants_are_its_only_properties_is_a_spec() {
        let spec = parse(&COUNTER.replace("def init_is_zero : Prop := init.count = 0\n", ""))
            .expect("it parses");
        assert_eq!(spec.properties, ["Counter.count_below_three.always"]);
    }

    #[test]
    fn a_machine_in_an_unclosed_namespace_still_names_its_properties_from_the_root() {
        let spec = parse(&COUNTER.replace("\nend Counter\n", "\n")).expect("it parses");
        assert!(
            spec.source.contains(
                "def _root_.Counter.count_below_three.always : Prop := ∀ actions, _root_.Counter.count_below_three (_root_.Counter.run actions)"
            ),
            "{}",
            spec.source
        );
    }

    #[test]
    fn an_init_and_a_step_without_an_invariant_are_no_machine() {
        let text = "namespace Old\n\ndef init : Nat := 0\n\ndef step (n : Nat) : Nat := n + 1\n\ndef run : Nat := 1\n\ndef step_grows : Prop := ∀ n, n < step n\n\nend Old\n";
        let spec = parse(text).expect("it parses");
        assert_eq!(spec.machine, None);
        assert_eq!(spec.properties, ["Old.step_grows"]);
        assert_eq!(spec.source, text);
    }

    #[test]
    fn an_invariant_may_take_its_state_as_a_binder_and_carry_attributes() {
        let spec = parse(
            &COUNTER
                .replace(
                    "def count_below_three : State → Prop := fun s => s.count < 3",
                    "@[simp] def count_below_three (s : State) : Prop := s.count < 3",
                )
                .replace("def init : State := ⟨0⟩", "abbrev init : State := ⟨0⟩"),
        )
        .expect("it parses");
        assert_eq!(
            spec.properties,
            ["Counter.init_is_zero", "Counter.count_below_three.always"]
        );
    }

    #[test]
    fn a_machine_that_defines_run_is_refused() {
        let refused = parse(&COUNTER.replace(
            "end Counter",
            "def run (actions : List Action) : State := actions.foldl step init\n\nend Counter",
        ));
        assert!(
            matches!(refused, Err(SpecError::MachineRun(_))),
            "{refused:?}"
        );
    }

    #[test]
    fn the_search_derives_the_machine_types_and_unfolds_each_invariant() {
        let spec = parse(COUNTER).expect("it parses");
        let search = spec.search(&["Counter.count_below_three.always"]);
        for line in [
            "deriving instance Plausible.Arbitrary for Counter.Action",
            "deriving instance Plausible.Shrinkable for Counter.State",
            "deriving instance Repr for Counter.Action",
            "open FormalRefute in example : _root_.Counter.count_below_three.always := by unfold _root_.Counter.count_below_three.always _root_.Counter.count_below_three; plausible",
        ] {
            assert!(search.lean_code.contains(line), "{line}");
        }
    }

    #[test]
    fn the_search_key_is_its_own() {
        let spec = demo();
        assert_ne!(
            spec.search_key("Demo.double_even"),
            spec.key("Demo.double_even")
        );
        assert_ne!(
            spec.search_key("Demo.double_even"),
            spec.search_key("Demo.double_mono")
        );
    }

    #[test]
    fn the_answers_key_is_not_the_key_of_a_property_of_the_same_name() {
        let spec = demo();
        assert_ne!(
            spec.answers_key("Demo.double_even"),
            spec.key("Demo.double_even")
        );
        assert_ne!(
            spec.answers_key("Demo.double"),
            parse(&DEMO.replace("n + n", "2 * n"))
                .expect("it parses")
                .answers_key("Demo.double")
        );
    }

    #[test]
    fn a_line_outside_the_proof_maps_to_nothing() {
        let composed = demo().compose("Demo.double_even", "theorem t : True := trivial");
        assert_eq!(composed.proof_line(1), None);
        assert_eq!(composed.proof_line(composed.offset), None);
        assert_eq!(composed.proof_line(composed.offset + 1), Some(1));
        assert_eq!(composed.proof_line(composed.offset + 2), None);
    }

    const TEXT: &str = "import Mathlib\n\nnamespace Text\n\ndef blank (s : List Char) : Bool := s.all (· = ' ')\n\nend Text\n";

    const USES: &str = "import Spec.Text\n\nnamespace Uses\n\ndef blank_is_all_space : Prop := ∀ s, Text.blank s = true → ∀ c ∈ s, c = ' '\n\nend Uses\n";

    fn write(dir: &TempDir, name: &str, text: &str) -> String {
        let path = dir.path().join(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("a directory");
        }
        fs::write(&path, text).expect("written");
        path.to_string_lossy().to_string()
    }

    #[test]
    fn an_imported_spec_comes_before_the_spec_and_its_imports_go_to_the_top() {
        let dir = TempDir::new().expect("a temporary directory");
        write(&dir, "Text.lean", TEXT);
        let spec = LeanSpec::load(&write(&dir, "Uses.lean", USES)).expect("it loads");
        assert_eq!(spec.properties, ["Uses.blank_is_all_space"]);
        assert!(
            spec.source.starts_with("import Mathlib\n"),
            "{}",
            spec.source
        );
        assert!(!spec.source.contains("Spec.Text"), "{}", spec.source);
        let text = spec
            .source
            .find("namespace Text")
            .expect("the import is in");
        let uses = spec.source.find("namespace Uses").expect("the spec is in");
        assert!(text < uses, "{}", spec.source);
        let composed = spec.compose("Uses.blank_is_all_space", "theorem t : True := trivial");
        assert!(
            composed.lean_code.starts_with("import Mathlib\n"),
            "{}",
            composed.lean_code
        );
        assert!(
            composed.lean_code.contains("namespace Text"),
            "{}",
            composed.lean_code
        );
    }

    #[test]
    fn a_spec_without_a_spec_import_reads_as_its_own_text() {
        let dir = TempDir::new().expect("a temporary directory");
        let text = TEXT.replace("end Text", "def p : Prop := True\n\nend Text");
        let spec = LeanSpec::load(&write(&dir, "Text.lean", &text)).expect("it loads");
        assert_eq!(spec.source, text);
    }

    #[test]
    fn an_edit_to_an_imported_spec_moves_the_keys_of_the_spec() {
        let dir = TempDir::new().expect("a temporary directory");
        write(&dir, "Text.lean", TEXT);
        let path = write(&dir, "Uses.lean", USES);
        let before = LeanSpec::load(&path)
            .expect("it loads")
            .key("Uses.blank_is_all_space");
        write(&dir, "Text.lean", &TEXT.replace("(· = ' ')", "(· == ' ')"));
        let after = LeanSpec::load(&path)
            .expect("it loads")
            .key("Uses.blank_is_all_space");
        assert_ne!(before, after);
    }

    #[test]
    fn a_spec_imported_twice_comes_in_once_and_a_nested_name_is_a_directory() {
        let dir = TempDir::new().expect("a temporary directory");
        write(&dir, "Lib/Text.lean", TEXT);
        write(
            &dir,
            "Words.lean",
            "import Spec.Lib.Text\n\nnamespace Words\n\ndef none : List Char := []\n\nend Words\n",
        );
        let path = write(
            &dir,
            "Uses.lean",
            &USES.replace(
                "import Spec.Text",
                "import Spec.Lib.Text\nimport Spec.Words",
            ),
        );
        let spec = LeanSpec::load(&path).expect("it loads");
        assert_eq!(
            spec.source.matches("namespace Text").count(),
            1,
            "{}",
            spec.source
        );
        assert!(spec.source.find("namespace Text") < spec.source.find("namespace Words"));
    }

    #[test]
    fn every_import_resolves_from_the_directory_of_the_spec_the_session_opens_on() {
        let dir = TempDir::new().expect("a temporary directory");
        write(&dir, "Text.lean", TEXT);
        write(
            &dir,
            "Lib/Inner.lean",
            "import Spec.Text\n\nnamespace Inner\n\nend Inner\n",
        );
        let top = write(
            &dir,
            "Top.lean",
            &USES.replace("import Spec.Text", "import Spec.Lib.Inner"),
        );
        assert!(LeanSpec::load(&top).is_ok(), "{:?}", LeanSpec::load(&top));
        let inner = write(
            &dir,
            "Lib/Inner.lean",
            "import Spec.Text\n\nnamespace Inner\n\ndef p : Prop := True\n\nend Inner\n",
        );
        assert!(
            matches!(LeanSpec::load(&inner), Err(SpecError::NoSuchImport { ref path, .. }) if path.ends_with("Lib/Text.lean")),
            "{:?}",
            LeanSpec::load(&inner)
        );
    }

    #[test]
    fn a_missing_import_a_cycle_and_an_import_that_runs_code_are_refused() {
        let dir = TempDir::new().expect("a temporary directory");
        let path = write(&dir, "Uses.lean", USES);
        assert!(
            matches!(LeanSpec::load(&path), Err(SpecError::NoSuchImport { ref import, .. }) if import == "Spec.Text"),
            "{:?}",
            LeanSpec::load(&path)
        );
        write(
            &dir,
            "Text.lean",
            &format!("import Spec.Uses\n{TEXT}").replace(
                "import Spec.Uses\nimport Mathlib",
                "import Mathlib\nimport Spec.Uses",
            ),
        );
        assert!(
            matches!(LeanSpec::load(&path), Err(SpecError::ImportCycle { .. })),
            "{:?}",
            LeanSpec::load(&path)
        );
        write(&dir, "Text.lean", &format!("{TEXT}\n#eval 1\n"));
        assert!(
            matches!(LeanSpec::load(&path), Err(SpecError::RunsCode { ref found, .. }) if found == "#eval"),
            "{:?}",
            LeanSpec::load(&path)
        );
    }
}
