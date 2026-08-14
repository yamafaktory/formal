//! Python string semantics the cache key depends on.
//!
//! The key is a digest of text that Python produced for months, and the golden
//! digests in `tests/fixtures/cache_keys.json` were recorded from it. Where
//! Python and Rust disagree about what a character or a line is, Python is the
//! specification: a divergence here does not produce a wrong answer, it produces
//! a key nobody ever hits again.

/// `str.isspace()`, which is wider than Rust's `char::is_whitespace`.
///
/// The four separator controls U+001C..U+001F are whitespace to Python and not
/// to the Unicode `White_Space` property Rust follows.
#[must_use]
pub fn is_space(c: char) -> bool {
    c.is_whitespace() || ('\u{1c}'..='\u{1f}').contains(&c)
}

/// `str.strip()`.
#[must_use]
pub fn strip(s: &str) -> &str {
    s.trim_matches(is_space)
}

/// `str.rstrip()`.
#[must_use]
pub fn rstrip(s: &str) -> &str {
    s.trim_end_matches(is_space)
}

/// `str.splitlines()`, which breaks on more than `\n` and `\r\n`.
///
/// Rust's `str::lines` knows two line boundaries; Python knows eleven, and a
/// vertical tab or a U+2028 inside a pasted function is enough for the two to
/// disagree about how many lines it has.
#[must_use]
pub fn splitlines(s: &str) -> Vec<&str> {
    let mut lines = Vec::new();
    let mut start = 0;
    let mut chars = s.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        let width = match c {
            '\n' | '\u{b}' | '\u{c}' | '\u{1c}' | '\u{1d}' | '\u{1e}' | '\u{85}' | '\u{2028}'
            | '\u{2029}' => c.len_utf8(),
            '\r' => {
                if chars.peek().map(|&(_, next)| next) == Some('\n') {
                    chars.next();
                    1 + '\n'.len_utf8()
                } else {
                    1
                }
            }
            _ => continue,
        };
        lines.push(&s[start..i]);
        start = i + width;
    }
    if start < s.len() {
        lines.push(&s[start..]);
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn separator_controls_are_whitespace_to_python() {
        assert!(is_space('\u{1c}'));
        assert!(!'\u{1c}'.is_whitespace());
    }

    #[test]
    fn a_trailing_newline_does_not_make_an_empty_last_line() {
        assert_eq!(splitlines("a\nb\n"), vec!["a", "b"]);
        assert_eq!(splitlines("a\nb"), vec!["a", "b"]);
    }

    #[test]
    fn a_blank_line_in_the_middle_survives() {
        assert_eq!(splitlines("a\n\nb"), vec!["a", "", "b"]);
    }

    #[test]
    fn crlf_is_one_boundary_and_a_bare_cr_is_another() {
        assert_eq!(splitlines("a\r\nb\rc"), vec!["a", "b", "c"]);
    }

    #[test]
    fn the_boundaries_rust_does_not_know_still_split() {
        assert_eq!(
            splitlines("a\u{b}b\u{2028}c\u{85}d"),
            vec!["a", "b", "c", "d"]
        );
    }

    #[test]
    fn nothing_splits_the_empty_string() {
        assert!(splitlines("").is_empty());
    }
}
