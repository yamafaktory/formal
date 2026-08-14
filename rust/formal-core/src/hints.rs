//! Match a Lean diagnostic to the advice for it.
//!
//! The advice used to be a 434-line `if ... in data` chain inside the verifier —
//! a third of that module and the largest single thing a rewrite has to
//! reproduce. Almost all of it was text. `guidance/hints.toml` holds the rules in
//! the order they are tried, and this module is only the matcher.
//!
//! Two consequences worth keeping in mind when editing the table. Order is the
//! semantics: `omega_on_a_string_literal` has to be tried before
//! `omega_beyond_linear_arithmetic` or the general answer swallows the specific
//! one, and the corpus test fails when it does. And a rule that produces nothing
//! — a handler whose pattern did not match — is not a match at all, so the search
//! continues with the next sibling and then the parent's own advice. That is what
//! let the old chain fall through a nested `if`.

use std::{
    collections::{
        BTreeMap,
        BTreeSet,
    },
    sync::OnceLock,
};

use regex::Regex;
use serde::Deserialize;
use thiserror::Error;

/// The shipped table, compiled in beside the code that reads it.
///
/// The text is a data file under version control, which is the point of it not
/// being Rust; a binary that has to find that file at runtime is a worse way to
/// get there than embedding it. While the Python still serves, both read these
/// same bytes, so the table cannot drift between the two.
const DATA: &str = include_str!("../../../src/formal/guidance/hints.toml");

/// Where the shipped table lives, for messages about it.
const ORIGIN: &str = "src/formal/guidance/hints.toml";

/// The table format this formal understands.
const SCHEMA_VERSION: u64 = 1;

/// The hint table cannot be trusted to answer anything.
#[derive(Clone, Debug, Error)]
pub enum HintTableError {
    /// The bytes are not TOML, or not the shape a table has.
    #[error("{ORIGIN} is not valid TOML: {0}")]
    NotToml(String),

    /// The table announces a format this formal does not read.
    #[error("{ORIGIN} is version {0}, this formal understands {SCHEMA_VERSION}")]
    Version(u64),

    /// Nothing would answer an unrecognised error.
    #[error("{ORIGIN} has no fallback, so an unrecognised error would get no answer")]
    NoFallback,

    /// There is nothing to match against.
    #[error("{ORIGIN} lists no rules")]
    NoRules,

    /// Two rules answer to one name, so one of them can never be spoken about.
    #[error("{ORIGIN}: duplicate rule id {0}")]
    DuplicateId(String),

    /// A rule offers advice two ways, and which one wins would be an accident.
    #[error("{ORIGIN}: {0} gives more than one answer")]
    AmbiguousAnswer(String),

    /// A rule can match but says nothing, which reads as a fall-through.
    #[error("{ORIGIN}: {0} can match but has no answer")]
    NoAnswer(String),

    /// A rule points at text that is not in the table.
    #[error("{ORIGIN}: {rule} refers to unknown text {name}")]
    UnknownText {
        /// The rule that points at it.
        rule: String,
        /// The name it points at.
        name: String,
    },

    /// A handler is named by a rule but never configured.
    #[error("{ORIGIN}: no configuration for handler {0}")]
    UnconfiguredHandler(String),
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "snake_case")]
enum HandlerName {
    KnownRename,
    LocalHypothesis,
    OptionInnerType,
    HypothesisIsFunction,
    FunctionExpectedLemma,
    TacticFailed,
}

impl HandlerName {
    fn as_str(self) -> &'static str {
        match self {
            Self::KnownRename => "known_rename",
            Self::LocalHypothesis => "local_hypothesis",
            Self::OptionInnerType => "option_inner_type",
            Self::HypothesisIsFunction => "hypothesis_is_function",
            Self::FunctionExpectedLemma => "function_expected_lemma",
            Self::TacticFailed => "tactic_failed",
        }
    }
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct KnownRename {
    template: String,
    renames: BTreeMap<String, String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct LocalHypothesis {
    template: String,
    split_ifs_suffix: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Templated {
    template: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct HypothesisIsFunction {
    template: String,
    default_name: String,
    default_required: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FunctionExpectedLemma {
    template: String,
    default_name: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct TacticFailed {
    template: String,
    suffix: String,
    tactics: BTreeMap<String, String>,
}

#[derive(Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct Handlers {
    known_rename: Option<KnownRename>,
    local_hypothesis: Option<LocalHypothesis>,
    option_inner_type: Option<Templated>,
    hypothesis_is_function: Option<HypothesisIsFunction>,
    function_expected_lemma: Option<FunctionExpectedLemma>,
    tactic_failed: Option<TacticFailed>,
}

impl Handlers {
    fn is_configured(&self, name: HandlerName) -> bool {
        match name {
            HandlerName::KnownRename => self.known_rename.is_some(),
            HandlerName::LocalHypothesis => self.local_hypothesis.is_some(),
            HandlerName::OptionInnerType => self.option_inner_type.is_some(),
            HandlerName::HypothesisIsFunction => self.hypothesis_is_function.is_some(),
            HandlerName::FunctionExpectedLemma => self.function_expected_lemma.is_some(),
            HandlerName::TacticFailed => self.tactic_failed.is_some(),
        }
    }
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Rule {
    id: String,
    #[serde(default)]
    all: Vec<String>,
    #[serde(default)]
    any: Vec<Vec<String>>,
    equals: Option<String>,
    #[serde(default)]
    lower: bool,
    hint: Option<String>,
    hint_ref: Option<String>,
    handler: Option<HandlerName>,
    #[serde(default)]
    sub: Vec<Rule>,
}

impl Rule {
    fn answers(&self) -> usize {
        usize::from(self.hint.is_some())
            + usize::from(self.hint_ref.is_some())
            + usize::from(self.handler.is_some())
    }

    /// Whether this rule claims the diagnostic, before asking what it would say.
    fn matches(&self, data: &str) -> bool {
        if let Some(equals) = &self.equals {
            return data == equals;
        }
        let lowered;
        let subject = if self.lower {
            lowered = data.to_lowercase();
            lowered.as_str()
        } else {
            data
        };
        if self.all.iter().any(|term| !subject.contains(term.as_str())) {
            return false;
        }
        self.any.is_empty()
            || self
                .any
                .iter()
                .any(|group| group.iter().all(|term| subject.contains(term.as_str())))
    }
}

/// The rules, the text they share, and the advice for everything unrecognised.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Table {
    version: u64,
    fallback: String,
    #[serde(default)]
    text: BTreeMap<String, String>,
    #[serde(default)]
    handler: Handlers,
    #[serde(default, rename = "rule")]
    rules: Vec<Rule>,
}

fn pattern(source: &'static str, cell: &'static OnceLock<Regex>) -> &'static Regex {
    cell.get_or_init(|| Regex::new(source).expect("the patterns are literals checked by the tests"))
}

macro_rules! captured {
    ($data:expr, $source:literal) => {{
        static CELL: OnceLock<Regex> = OnceLock::new();
        pattern($source, &CELL).captures($data)
    }};
}

fn fill(template: &str, values: &[(&str, &str)]) -> String {
    let mut filled = template.to_string();
    for (key, value) in values {
        filled = filled.replace(&format!("{{{key}}}"), value);
    }
    filled
}

impl Table {
    /// Read a table, refusing one that could answer wrongly or not at all.
    ///
    /// # Errors
    ///
    /// [`HintTableError`] for TOML that will not parse, a version this formal
    /// does not read, or a rule that is ambiguous, silent, duplicated, or points
    /// at text or a handler configuration that is not there.
    pub fn parse(source: &str) -> Result<Self, HintTableError> {
        let table: Self =
            toml::from_str(source).map_err(|e| HintTableError::NotToml(e.to_string()))?;
        table.validate()?;
        Ok(table)
    }

    /// The table shipped with this formal, parsed once.
    ///
    /// # Errors
    ///
    /// As [`Table::parse`]. A failure here is a build-time mistake rather than
    /// anything a caller did, and the corpus test catches it first.
    pub fn shipped() -> Result<&'static Self, HintTableError> {
        static TABLE: OnceLock<Result<Table, HintTableError>> = OnceLock::new();
        TABLE
            .get_or_init(|| Table::parse(DATA))
            .as_ref()
            .map_err(Clone::clone)
    }

    fn validate(&self) -> Result<(), HintTableError> {
        if self.version != SCHEMA_VERSION {
            return Err(HintTableError::Version(self.version));
        }
        if self.fallback.is_empty() {
            return Err(HintTableError::NoFallback);
        }

        let mut seen = BTreeSet::new();
        self.walk(&self.rules, "", &mut seen)?;
        if seen.is_empty() {
            return Err(HintTableError::NoRules);
        }
        Ok(())
    }

    fn walk(
        &self,
        rules: &[Rule],
        path: &str,
        seen: &mut BTreeSet<String>,
    ) -> Result<(), HintTableError> {
        for rule in rules {
            let rule_id = format!("{path}{}", rule.id);
            if !seen.insert(rule_id.clone()) {
                return Err(HintTableError::DuplicateId(rule_id));
            }
            let answers = rule.answers();
            if answers > 1 {
                return Err(HintTableError::AmbiguousAnswer(rule_id));
            }
            if answers == 0 && rule.sub.is_empty() {
                return Err(HintTableError::NoAnswer(rule_id));
            }
            if let Some(name) = &rule.hint_ref
                && !self.text.contains_key(name)
            {
                return Err(HintTableError::UnknownText {
                    rule: rule_id,
                    name: name.clone(),
                });
            }
            if let Some(handler) = rule.handler
                && !self.handler.is_configured(handler)
            {
                return Err(HintTableError::UnconfiguredHandler(
                    handler.as_str().to_string(),
                ));
            }
            self.walk(&rule.sub, &format!("{rule_id}/"), seen)?;
        }
        Ok(())
    }

    /// The advice for one Lean diagnostic, or the fallback when nothing claims it.
    #[must_use]
    pub fn hint_for(&self, data: &str) -> String {
        self.lookup(data, &mut BTreeSet::new())
    }

    /// Every rule that claimed this diagnostic, whether or not it answered.
    ///
    /// A rule the corpus cannot reach is either dead or shadowed by an earlier
    /// one, and both are silent: the table still loads, and the only symptom is
    /// advice nobody ever gets.
    #[must_use]
    pub fn matched_rule_ids(&self, data: &str) -> BTreeSet<String> {
        let mut fired = BTreeSet::new();
        self.lookup(data, &mut fired);
        fired
    }

    /// Every rule in the table, sub-rules included.
    #[must_use]
    pub fn rule_ids(&self) -> BTreeSet<String> {
        fn collect(rules: &[Rule], found: &mut BTreeSet<String>) {
            for rule in rules {
                found.insert(rule.id.clone());
                collect(&rule.sub, found);
            }
        }
        let mut found = BTreeSet::new();
        collect(&self.rules, &mut found);
        found
    }

    fn lookup(&self, data: &str, fired: &mut BTreeSet<String>) -> String {
        for rule in &self.rules {
            if rule.matches(data) {
                fired.insert(rule.id.clone());
                if let Some(hint) = self.answer(rule, data, fired) {
                    return hint;
                }
            }
        }
        self.fallback.clone()
    }

    fn answer(&self, rule: &Rule, data: &str, fired: &mut BTreeSet<String>) -> Option<String> {
        for sub in &rule.sub {
            if sub.matches(data) {
                fired.insert(sub.id.clone());
                if let Some(hint) = self.answer(sub, data, fired) {
                    return Some(hint);
                }
            }
        }
        if let Some(handler) = rule.handler {
            return self.run(handler, data);
        }
        if let Some(name) = &rule.hint_ref {
            return self.text.get(name).cloned();
        }
        rule.hint.clone()
    }

    fn run(&self, handler: HandlerName, data: &str) -> Option<String> {
        match handler {
            HandlerName::KnownRename => self.known_rename(data),
            HandlerName::LocalHypothesis => self.local_hypothesis(data),
            HandlerName::OptionInnerType => self.option_inner_type(data),
            HandlerName::HypothesisIsFunction => self.hypothesis_is_function(data),
            HandlerName::FunctionExpectedLemma => self.function_expected_lemma(data),
            HandlerName::TacticFailed => self.tactic_failed(data),
        }
    }

    fn known_rename(&self, data: &str) -> Option<String> {
        let config = self.handler.known_rename.as_ref()?;
        let found = captured!(
            data,
            r"[Uu]nknown (?:identifier|constant) [`']([A-Za-z_.][A-Za-z0-9_.']*)[`']"
        )?;
        let name = &found[1];
        let replacement = config.renames.get(name)?;
        Some(fill(
            &config.template,
            &[("name", name), ("replacement", replacement)],
        ))
    }

    fn local_hypothesis(&self, data: &str) -> Option<String> {
        let config = self.handler.local_hypothesis.as_ref()?;
        let found = captured!(
            data,
            r"[Uu]nknown identifier [`']((?:h|ih)[a-z]{0,4}[0-9']*)[`']"
        )?;
        let mut hint = fill(&config.template, &[("name", &found[1])]);
        if data.contains("split_ifs") {
            hint.push_str(&config.split_ifs_suffix);
        }
        Some(hint)
    }

    fn option_inner_type(&self, data: &str) -> Option<String> {
        let config = self.handler.option_inner_type.as_ref()?;
        let found = captured!(data, r"has type\s+Option (\S+)")?;
        let needed = captured!(data, r"expected to have type\s+Option (\S+)")?;
        if found[1] == needed[1] {
            return None;
        }
        Some(fill(
            &config.template,
            &[("found", &found[1]), ("needed", &needed[1])],
        ))
    }

    fn hypothesis_is_function(&self, data: &str) -> Option<String> {
        let config = self.handler.hypothesis_is_function.as_ref()?;
        let named = captured!(data, r"The argument\s+(\w+)\s+has type");
        let arrow = captured!(data, r"has type\s+(.+?)\s+→");
        let name = named
            .as_ref()
            .map_or(config.default_name.as_str(), |caps| &caps[1]);
        let required = arrow
            .as_ref()
            .map_or(config.default_required.as_str(), |caps| caps[1].trim());
        Some(fill(
            &config.template,
            &[("name", name), ("required", required)],
        ))
    }

    fn function_expected_lemma(&self, data: &str) -> Option<String> {
        let config = self.handler.function_expected_lemma.as_ref()?;
        let named = captured!(data, r"Function expected at\s+(\S+)");
        Some(fill(
            &config.template,
            &[(
                "name",
                named
                    .as_ref()
                    .map_or(config.default_name.as_str(), |c| &c[1]),
            )],
        ))
    }

    fn tactic_failed(&self, data: &str) -> Option<String> {
        let config = self.handler.tactic_failed.as_ref()?;
        let found = captured!(data, r"[Tt]actic `([^`]+)` failed")?;
        let name = &found[1];
        let mut hint = fill(&config.template, &[("name", name)]);
        if let Some(specific) = config.tactics.get(name) {
            hint.push(' ');
            hint.push_str(specific);
        }
        hint.push_str(&config.suffix);
        Some(hint)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_shipped_table_parses_and_validates() {
        assert!(Table::shipped().is_ok());
    }

    #[test]
    fn a_table_from_another_version_is_refused() {
        let error = Table::parse("version = 99\nfallback = 'x'\n[[rule]]\nid = 'a'\nhint = 'b'")
            .expect_err("it is refused");
        assert!(error.to_string().contains("is version 99"), "{error}");
    }

    #[test]
    fn a_rule_answering_two_ways_is_refused() {
        let error = Table::parse(
            "version = 1\nfallback = 'x'\n[[rule]]\nid = 'a'\nhint = 'b'\nhint_ref = 'c'",
        )
        .expect_err("it is refused");
        assert!(
            error.to_string().contains("gives more than one answer"),
            "{error}"
        );
    }

    #[test]
    fn a_rule_that_says_nothing_is_refused() {
        let error = Table::parse("version = 1\nfallback = 'x'\n[[rule]]\nid = 'a'\nall = ['q']")
            .expect_err("it is refused");
        assert!(
            error.to_string().contains("can match but has no answer"),
            "{error}"
        );
    }

    #[test]
    fn a_table_with_no_fallback_is_refused() {
        let error = Table::parse("version = 1\nfallback = ''\n[[rule]]\nid = 'a'\nhint = 'b'")
            .expect_err("it is refused");
        assert!(error.to_string().contains("no fallback"), "{error}");
    }

    #[test]
    fn a_dangling_text_reference_is_refused() {
        let error =
            Table::parse("version = 1\nfallback = 'x'\n[[rule]]\nid = 'a'\nhint_ref = 'nowhere'")
                .expect_err("it is refused");
        assert!(
            error.to_string().contains("unknown text nowhere"),
            "{error}"
        );
    }

    #[test]
    fn a_handler_with_no_configuration_is_refused() {
        let error = Table::parse(
            "version = 1\nfallback = 'x'\n[[rule]]\nid = 'a'\nhandler = 'tactic_failed'",
        )
        .expect_err("it is refused");
        assert!(
            error.to_string().contains("no configuration for handler"),
            "{error}"
        );
    }

    #[test]
    fn two_rules_under_one_id_are_refused() {
        let error =
            Table::parse("version = 1\nfallback = 'x'\n[[rule]]\nid = 'a'\nhint = 'b'\n[[rule]]\nid = 'a'\nhint = 'c'")
                .expect_err("it is refused");
        assert!(error.to_string().contains("duplicate rule id a"), "{error}");
    }

    #[test]
    fn a_sub_rule_id_is_qualified_by_its_parent() {
        let table = Table::parse(
            "version = 1\nfallback = 'x'\n[[rule]]\nid = 'a'\nhint = 'b'\n[[rule.sub]]\nid = 'a'\nhint = 'c'",
        )
        .expect("a sub-rule may repeat its parent's name");
        assert_eq!(table.rule_ids(), ["a".to_string()].into_iter().collect());
    }

    #[test]
    fn nothing_matching_gets_the_fallback() {
        let table = Table::parse(
            "version = 1\nfallback = 'try again'\n[[rule]]\nid = 'a'\nall = ['zzz']\nhint = 'b'",
        )
        .expect("the table is valid");
        assert_eq!(table.hint_for("something else"), "try again");
    }

    #[test]
    fn a_rule_that_matches_but_answers_nothing_falls_through_to_the_next() {
        let table = Table::parse(
            "version = 1\nfallback = 'x'\n[handler.tactic_failed]\ntemplate = 't'\nsuffix = ''\n\
             [handler.tactic_failed.tactics]\n[[rule]]\nid = 'a'\nall = ['boom']\nhandler = 'tactic_failed'\n\
             [[rule]]\nid = 'b'\nall = ['boom']\nhint = 'the next one'",
        )
        .expect("the table is valid");
        assert_eq!(table.hint_for("boom"), "the next one");
    }

    #[test]
    fn lower_folds_the_subject_and_not_the_terms() {
        let table = Table::parse("version = 1\nfallback = 'x'\n[[rule]]\nid = 'a'\nlower = true\nall = ['boom']\nhint = 'b'")
            .expect("the table is valid");
        assert_eq!(table.hint_for("BOOM"), "b");
    }

    #[test]
    fn equals_is_the_whole_diagnostic_and_not_a_substring() {
        let table = Table::parse(
            "version = 1\nfallback = 'x'\n[[rule]]\nid = 'a'\nequals = 'boom'\nhint = 'b'",
        )
        .expect("the table is valid");
        assert_eq!(table.hint_for("boom"), "b");
        assert_eq!(table.hint_for("boom and more"), "x");
    }
}
