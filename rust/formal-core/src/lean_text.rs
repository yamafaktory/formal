//! What a Lean source says once its comments are gone.

use std::sync::OnceLock;

use regex::Regex;

fn runs_code_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN.get_or_init(|| {
        Regex::new(
            r"#(?:eval|exit|guard)\w*|\b(?:run_\w+|by_elab|elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat|\w*initialize|unsafe\w*|implemented_by|extern|(?:command|term|tactic)_elab|delab|(?:E|Base)?IO|Lean)\b",
        )
        .expect("the pattern is a literal")
    })
}

/// `lean_code` with each comment replaced by a space, and its strings kept.
#[must_use]
pub fn without_comments(lean_code: &str) -> String {
    let mut kept = String::with_capacity(lean_code.len());
    let mut rest = lean_code;
    while let Some(c) = rest.chars().next() {
        if rest.starts_with("--") {
            let end = rest.find('\n').unwrap_or(rest.len());
            kept.push(' ');
            rest = &rest[end..];
        } else if rest.starts_with("/-") {
            kept.push(' ');
            rest = &rest[block_comment_len(rest)..];
        } else if c == '"' {
            let mut index = 1;
            let mut escaped = false;
            for (offset, next) in rest[1..].char_indices() {
                index = 1 + offset + next.len_utf8();
                if escaped {
                    escaped = false;
                } else if next == '\\' {
                    escaped = true;
                } else if next == '"' {
                    break;
                }
            }
            kept.push_str(&rest[..index]);
            rest = &rest[index..];
        } else if rest.starts_with("'\"'") {
            kept.push_str("'\"'");
            rest = &rest[3..];
        } else {
            kept.push(c);
            rest = &rest[c.len_utf8()..];
        }
    }
    kept
}

/// The first thing in `lean_code` that could run code while Lean elaborates it.
///
/// Such code could print what formal reads as Lean's verdict, so a proof that
/// contains any of it is refused rather than checked. Comments are ignored.
#[must_use]
pub fn runs_code(lean_code: &str) -> Option<String> {
    runs_code_pattern()
        .find(&without_comments(lean_code))
        .map(|found| found.as_str().to_string())
}

fn block_comment_len(rest: &str) -> usize {
    let mut depth = 0usize;
    let mut index = 0;
    while index < rest.len() {
        if rest[index..].starts_with("/-") {
            depth += 1;
            index += 2;
        } else if rest[index..].starts_with("-/") {
            depth -= 1;
            index += 2;
            if depth == 0 {
                break;
            }
        } else {
            index += rest[index..].chars().next().map_or(1, char::len_utf8);
        }
    }
    index.min(rest.len())
}

fn skip_trivia(code: &str, mut index: usize) -> usize {
    loop {
        let rest = &code[index..];
        let trimmed = rest.trim_start_matches(|c: char| c.is_whitespace() || c == '\u{feff}');
        index += rest.len() - trimmed.len();
        if trimmed.starts_with("--") {
            index += trimmed.find('\n').unwrap_or(trimmed.len());
        } else if trimmed.starts_with("/-") {
            index += block_comment_len(trimmed);
        } else {
            return index;
        }
    }
}

/// One `import <Module>` command in the header of a Lean file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Import {
    /// Where the command starts in the file.
    pub start: usize,
    /// Where its module name ends.
    pub end: usize,
    /// The module it imports.
    pub module: String,
}

/// The imports of `code`, in order. Comments may come before and between them.
#[must_use]
pub fn imports(code: &str) -> Vec<Import> {
    let mut found = Vec::new();
    let mut index = 0;
    loop {
        let start = skip_trivia(code, index);
        let Some(after) = code[start..].strip_prefix("import") else {
            return found;
        };
        let name_start = start + "import".len() + (after.len() - after.trim_start().len());
        if name_start == start + "import".len() {
            return found;
        }
        let name_len = code[name_start..]
            .find(|c: char| c.is_whitespace())
            .unwrap_or(code.len() - name_start);
        if name_len == 0 {
            return found;
        }
        let end = name_start + name_len;
        found.push(Import {
            start,
            end,
            module: code[name_start..end].to_string(),
        });
        index = end;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_import_inside_a_comment_is_not_one() {
        let code = "/- Copyright\nimport Fake -/\nimport Mathlib\n-- note\nimport Mathlib.Tactic\n\ntheorem t";
        let modules: Vec<String> = imports(code)
            .into_iter()
            .map(|import| import.module)
            .collect();
        assert_eq!(modules, ["Mathlib", "Mathlib.Tactic"]);
    }

    #[test]
    fn an_import_ends_with_its_module_name() {
        let code = "\u{feff}import Mathlib /- x\n-/\nimport  Mathlib.Tactic infixl:65 \" ++ \" => fun _ b => b\nimport Ignored";
        let found = imports(code);
        assert_eq!(found.len(), 2);
        assert_eq!(&code[found[0].start..found[0].end], "import Mathlib");
        assert_eq!(
            &code[found[1].start..found[1].end],
            "import  Mathlib.Tactic"
        );
        assert_eq!(imports("importance : Nat"), Vec::new());
    }
}
