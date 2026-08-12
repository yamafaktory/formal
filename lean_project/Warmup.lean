-- Pre-elaborates common Mathlib imports so the first proof request is fast.
-- Built by setup.sh, after the prebuilt oleans are fetched.
import Mathlib
import Mathlib.Tactic

-- Force full elaboration — without a declaration the compiler may skip elaboration.
theorem warmup : True := trivial
