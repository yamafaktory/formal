"""The record of what was established about one property.

Kept apart from whoever produced it. The proof cache persists these and the
session builds them, and neither should have to import a pipeline to name the
shape of its own result — proof_cache reached for it under TYPE_CHECKING and
again at call time to avoid the cycle that caused.
"""

from dataclasses import dataclass, field


@dataclass
class PropertyResult:
    property_id: str
    description: str
    kind: str
    function: str
    verified: bool
    lean_code: str
    lean_output: str
    retries: int
    reason: str = ""
    status: str = "failed"  # "verified" | "failed" | "unverifiable" | "error"
    fidelity: str = "unchecked"  # "ok" | "diverges" | "unchecked"
    back_translation: str = ""
    fidelity_reason: str = ""
    preconditions: list[str] = field(default_factory=list)
    assumptions: list[str] = field(default_factory=list)
    cached: bool = False
