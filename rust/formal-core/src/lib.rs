//! The pure logic of formal: what a property is, and what identifies it.
//!
//! Nothing here runs Lean or answers a request. It is the part of the service
//! that can be held to a fixture, and the fixtures it is held to were recorded
//! from the Python implementation this replaces.

pub mod proof_cache;
pub mod property;
pub mod pystr;
pub mod specs;
