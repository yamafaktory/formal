//! Everything formal needs the machine for: where Lean lives, and how it is confined.
//!
//! Separate from `formal-core` because none of it can be held to a fixture. What
//! it can be held to is the shape of the command it builds, which is the part
//! that decides whether caller-authored Lean is confined at all.

pub mod paths;
pub mod sandbox;
pub mod toolchain;
pub mod verifier;
