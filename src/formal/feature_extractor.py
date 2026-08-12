import json
import re
from dataclasses import dataclass, field

from . import prompts, proof_cache
from .llm_client import call_llm
from .logger import get_logger, log

_log = get_logger(__name__)

# Function-definition syntax across the supported languages. Used only to notice
# that a decomposition returning nothing is suspicious.
_DEFINITION = re.compile(
    r"(^|\s)(def|fn|func|function|fun|sub|proc)\s+\w+"
    r"|\w+\s+\w+\s*\([^)]*\)\s*(\{|:)"
    r"|=>\s*\{?",
    re.MULTILINE,
)


def looks_like_it_defines_functions(code: str) -> bool:
    return bool(_DEFINITION.search(code))


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
    preconditions: list[str] = field(default_factory=list)
    assumptions: list[str] = field(default_factory=list)
    # Set by screening step
    verifiable: bool = True
    unverifiable_reason: str = ""


@dataclass
class DecomposedFeature:
    feature_summary: str
    pure_functions: list[PureFunction]
    impure_parts: list[str]
    properties: list[Property]


def _feature_to_dict(feature: DecomposedFeature) -> dict:
    return {
        "feature_summary": feature.feature_summary,
        "pure_functions": [f.__dict__ for f in feature.pure_functions],
        "impure_parts": feature.impure_parts,
    }


def _feature_from_dict(data: dict) -> DecomposedFeature:
    return DecomposedFeature(
        feature_summary=data["feature_summary"],
        pure_functions=[PureFunction(**f) for f in data["pure_functions"]],
        impure_parts=data["impure_parts"],
        properties=[],
    )


def _decompose_cache_name(code: str, language: str) -> str:
    prompts_hash = proof_cache.json_key(prompts.DECOMPOSE_SYSTEM, prompts.DECOMPOSE_USER)[:8]
    return "decompose_" + proof_cache.json_key(prompts_hash, language, code)


def _properties_cache_name(feature: DecomposedFeature, language: str) -> str:
    prompts_hash = proof_cache.json_key(prompts.PROPERTY_EXTRACTION_SYSTEM, prompts.PROPERTY_EXTRACTION_USER)[:8]
    fingerprint = json.dumps(_feature_to_dict(feature), sort_keys=True)
    return "properties_" + proof_cache.json_key(prompts_hash, language, fingerprint)


def decompose(code: str, language: str = "Python") -> DecomposedFeature:
    """Step 1 — Split feature into pure functions and side effects.

    Decomposition is an LLM step and its output varies between runs on identical
    input — the same file has yielded several pure functions on one run and none
    on the next. An empty result on a file that plainly defines functions is
    retried once, since silently reporting "nothing to check" is the one failure
    mode a caller cannot distinguish from a clean pass.
    """
    name = _decompose_cache_name(code, language)
    cached = proof_cache.load_json(name)
    if cached is not None:
        log(_log, "CACHE", f"decomposition reused — {len(cached['pure_functions'])} pure function(s)")
        return _feature_from_dict(cached)

    feature = _decompose_once(code, language)
    if not feature.pure_functions and looks_like_it_defines_functions(code):
        log(_log, "PIPELINE", "Decomposition found no pure functions in a file that defines some — retrying")
        retried = _decompose_once(code, language)
        if retried.pure_functions:
            log(_log, "PIPELINE", f"Retry found {len(retried.pure_functions)} pure function(s)")
            feature = retried

    # An empty decomposition is never cached — it is the outcome most likely to be
    # a one-off LLM miss, and freezing it would make the miss permanent.
    if feature.pure_functions:
        proof_cache.save_json(name, _feature_to_dict(feature))
    return feature


def _decompose_once(code: str, language: str) -> DecomposedFeature:
    system = prompts.DECOMPOSE_SYSTEM
    user = prompts.DECOMPOSE_USER.format(code=code, language=language)
    data = None
    for _ in range(2):
        raw = call_llm(system, user)
        try:
            data = json.loads(_clean_json(raw))
            break
        except json.JSONDecodeError:
            continue
    if data is None:
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
    """Step 2 — Extract and screen properties in a single LLM call."""
    if not feature.pure_functions:
        return []

    pure_text = "\n\n".join(f"# {f.name}: {f.description}\n{f.code}" for f in feature.pure_functions)

    system = prompts.PROPERTY_EXTRACTION_SYSTEM
    user = prompts.PROPERTY_EXTRACTION_USER.format(
        language=language,
        pure_functions=pure_text,
        feature_summary=feature.feature_summary,
    )
    name = _properties_cache_name(feature, language)
    cached = proof_cache.load_json(name)
    if cached is not None:
        log(_log, "CACHE", f"property set reused — {len(cached.get('properties', []))} properties")
        return _parse_properties(cached)

    data = None
    for _ in range(2):
        raw = call_llm(system, user)
        try:
            data = json.loads(_clean_json(raw))
            break
        except json.JSONDecodeError:
            continue
    if data is None:
        return []

    properties = _parse_properties(data)
    if properties:
        proof_cache.save_json(name, data)
    return properties


def assign_unique_ids(properties: list["Property"]) -> list["Property"]:
    """Guarantee distinct ids — results are matched back to properties by id."""
    seen: set[str] = set()
    for position, prop in enumerate(properties, start=1):
        candidate = prop.id or f"prop_{position}"
        while candidate in seen:
            candidate = f"{candidate}_{position}"
        prop.id = candidate
        seen.add(candidate)
    return properties


def _parse_properties(data: dict) -> list["Property"]:
    properties = [
        Property(
            id=str(p.get("id") or "").strip(),
            description=p.get("description", ""),
            function=p.get("function", ""),
            kind=p.get("kind", "invariant"),
            formal=p.get("formal", ""),
            preconditions=p.get("preconditions", []),
            assumptions=p.get("assumptions", []),
            verifiable=p.get("verifiable", True),
            unverifiable_reason=p.get("unverifiable_reason", ""),
        )
        for p in data.get("properties", [])
    ]
    return assign_unique_ids(properties)


def _clean_json(text: str) -> str:
    """Strip markdown code fences if present."""
    text = text.strip()
    if text.startswith("```"):
        lines = text.split("\n")
        text = "\n".join(lines[1:-1] if lines[-1] == "```" else lines[1:])
    return text
