//! What formal does with a proof.
//!
//! The policy layer: what gets screened before Lean is paid for, what gets
//! batched, what gets retried without asking anyone, and what has earned a place
//! in a cache that outlives the run.

pub mod checker;
