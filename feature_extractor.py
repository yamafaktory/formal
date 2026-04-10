import json
from dataclasses import dataclass

from . import prompts
from .llm_client import call_llm as call_claude


@dataclass
class PureFunction:
    name: str
    code: str
    description: str


@dataclass
class Property:
    id: str
    description: str
    function: str
    kind: str
    formal: str
    # Set by screening step
    verifiable: bool = True
    unverifiable_reason: str = ""


@dataclass
class DecomposedFeature:
    feature_summary: str
    pure_functions: list[PureFunction]
    impure_parts: list[str]
    properties: list[Property]


def decompose(code: str, language: str = "Python") -> DecomposedFeature:
    """Step 1 — Split feature into pure functions and side effects."""
    raw = call_claude(
        prompts.DECOMPOSE_SYSTEM,
        prompts.DECOMPOSE_USER.format(code=code, language=language),
    )
    try:
        data = json.loads(_clean_json(raw))
    except json.JSONDecodeError:
        return DecomposedFeature(
            feature_summary="Could not parse feature",
            pure_functions=[],
            impure_parts=["JSON parse error on decomposition"],
            properties=[],
        )

    pure_functions = [
        PureFunction(
            name=f.get("name", "unknown"),
            code=f.get("code", ""),
            description=f.get("description", ""),
        )
        for f in data.get("pure_functions", [])
    ]

    return DecomposedFeature(
        feature_summary=data.get("feature_summary", ""),
        pure_functions=pure_functions,
        impure_parts=data.get("impure_parts", []),
        properties=[],
    )


def extract_properties(feature: DecomposedFeature, language: str = "Python") -> list[Property]:
    """Step 2 — Extract verifiable properties from pure functions."""
    if not feature.pure_functions:
        return []

    pure_text = "\n\n".join(f"# {f.name}: {f.description}\n{f.code}" for f in feature.pure_functions)

    raw = call_claude(
        prompts.PROPERTY_EXTRACTION_SYSTEM,
        prompts.PROPERTY_EXTRACTION_USER.format(
            pure_functions=pure_text,
            feature_summary=feature.feature_summary,
        ),
    )

    try:
        data = json.loads(_clean_json(raw))
    except json.JSONDecodeError:
        return []

    return [
        Property(
            id=p.get("id", f"prop_{i}"),
            description=p.get("description", ""),
            function=p.get("function", ""),
            kind=p.get("kind", "invariant"),
            formal=p.get("formal", ""),
        )
        for i, p in enumerate(data.get("properties", []))
    ]


def screen_properties(properties: list[Property], language: str = "Python") -> list[Property]:
    """Step 3 — Pre-screen properties for Lean 4 formalizability.

    Marks each property as verifiable or unverifiable before attempting Lean.
    This avoids wasting retries on properties that cannot be modelled mathematically.
    """
    if not properties:
        return properties

    props_text = json.dumps(
        [{"id": p.id, "description": p.description, "formal": p.formal, "kind": p.kind} for p in properties], indent=2
    )

    raw = call_claude(
        prompts.PROPERTY_SCREENING_SYSTEM,
        prompts.PROPERTY_SCREENING_USER.format(
            language=language,
            properties=props_text,
        ),
    )

    try:
        data = json.loads(_clean_json(raw))
    except json.JSONDecodeError:
        # If screening fails, assume all are verifiable
        return properties

    assessments = {a["id"]: a for a in data.get("assessments", [])}

    for prop in properties:
        assessment = assessments.get(prop.id, {})
        prop.verifiable = assessment.get("verifiable", True)
        if not prop.verifiable:
            prop.unverifiable_reason = assessment.get("reason", "Could not be formalized in Lean 4")

    return properties


def _clean_json(text: str) -> str:
    """Strip markdown code fences if present."""
    text = text.strip()
    if text.startswith("```"):
        lines = text.split("\n")
        text = "\n".join(lines[1:-1] if lines[-1] == "```" else lines[1:])
    return text
