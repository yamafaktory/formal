-- Pre-elaborates common Mathlib imports so the first proof request is fast.
-- Built at image build time; oleans are baked into the Docker layer.
import Mathlib
import Mathlib.Tactic

-- Force full elaboration — without a declaration the compiler may skip elaboration.
theorem warmup : True := trivial
