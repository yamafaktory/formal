//! Tagged lines on stderr, coloured when someone is there to see them.

use std::io::{
    IsTerminal,
    Write,
    stderr,
};

/// What a line is about, which decides its label and its colour.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Tag {
    /// The run as a whole.
    Pipeline,
    /// Screening before anything expensive happens.
    Screen,
    /// A proof being checked.
    Verify,
    /// Lean itself.
    Lean,
    /// Something worked.
    Ok,
    /// Something did not.
    Fail,
    /// The proof cache.
    Cache,
    /// A session opening, closing or expiring.
    Session,
}

impl Tag {
    fn label(self) -> &'static str {
        match self {
            Self::Pipeline => "PIPELINE",
            Self::Screen => "SCREEN  ",
            Self::Verify => "VERIFY  ",
            Self::Lean => "LEAN    ",
            Self::Ok => "OK      ",
            Self::Fail => "FAIL    ",
            Self::Cache => "CACHE   ",
            Self::Session => "SESSION ",
        }
    }

    fn colour(self) -> &'static str {
        match self {
            Self::Pipeline => "\x1b[36m",
            Self::Screen => "\x1b[35m",
            Self::Verify => "\x1b[33m",
            Self::Ok => "\x1b[32m",
            Self::Fail => "\x1b[31m",
            Self::Lean | Self::Cache | Self::Session => "\x1b[90m",
        }
    }
}

fn coloured() -> bool {
    stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none()
}

/// Render one line exactly as it would be written.
#[must_use]
pub fn line(tag: Tag, message: &str, coloured: bool) -> String {
    if coloured {
        format!("\x1b[1m{}[{}]\x1b[0m {message}", tag.colour(), tag.label())
    } else {
        format!("[{}] {message}", tag.label())
    }
}

/// Say something on stderr, and say nothing about it if that fails.
pub fn log(tag: Tag, message: &str) {
    let _ = writeln!(stderr(), "{}", line(tag, message, coloured()));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_plain_line_is_the_tag_and_the_message() {
        assert_eq!(line(Tag::Ok, "p1 proved", false), "[OK      ] p1 proved");
    }

    #[test]
    fn every_label_is_the_same_width() {
        for tag in [
            Tag::Pipeline,
            Tag::Screen,
            Tag::Verify,
            Tag::Lean,
            Tag::Ok,
            Tag::Fail,
            Tag::Cache,
            Tag::Session,
        ] {
            assert_eq!(tag.label().len(), 8, "{tag:?}");
        }
    }

    #[test]
    fn a_coloured_line_still_ends_with_the_message() {
        let rendered = line(Tag::Fail, "p1 rejected", true);
        assert!(rendered.ends_with(" p1 rejected"), "{rendered}");
        assert!(rendered.contains("\x1b[31m"), "{rendered}");
    }
}
