"""Does the proved theorem say what the property said?

Lean guarantees only that the theorem it was handed is true. If formalization
misread the property, Lean proves the wrong thing and reports success — the one
failure mode that produces false confidence rather than a visible failure.

Reading the theorem back into English without sight of the original description,
then comparing the two, is a round-trip check on that translation. It is a weaker
instrument than the proof itself: the model that mistranslated is also the one
judging, so treat a divergence as a prompt to read the theorem, not a verdict.
"""

import json
from dataclasses import dataclass

from . import prompts, proof_cache
from .feature_extractor import _clean_json
from .llm_client import BackendUnavailable, call_llm
from .logger import get_logger, log

_log = get_logger(__name__)

OK = "ok"
DIVERGES = "diverges"
UNCHECKED = "unchecked"


@dataclass
class Fidelity:
    verdict: str = UNCHECKED
    back_translation: str = ""
    reason: str = ""


def _cache_name(description: str, lean_code: str) -> str:
    prompts_hash = proof_cache.json_key(
        prompts.BACK_TRANSLATE_SYSTEM,
        prompts.BACK_TRANSLATE_USER,
        prompts.FIDELITY_JUDGE_SYSTEM,
        prompts.FIDELITY_JUDGE_USER,
    )[:8]
    return "fidelity_" + proof_cache.json_key(prompts_hash, description, lean_code)


def back_translate(lean_code: str) -> str:
    """Describe the theorem without showing the model what it was meant to say."""
    return call_llm(
        prompts.BACK_TRANSLATE_SYSTEM,
        prompts.BACK_TRANSLATE_USER.format(lean_code=lean_code),
    ).strip()


def judge(description: str, back_translation: str) -> tuple[bool, str]:
    raw = call_llm(
        prompts.FIDELITY_JUDGE_SYSTEM,
        prompts.FIDELITY_JUDGE_USER.format(description=description, back_translation=back_translation),
    )
    try:
        data = json.loads(_clean_json(raw))
    except json.JSONDecodeError:
        return True, "fidelity judge returned unparseable output"
    return bool(data.get("agrees", True)), str(data.get("reason", "")).strip()


def check(description: str, lean_code: str) -> Fidelity:
    """Round-trip a proved theorem back to English and compare it to the property."""
    if not lean_code.strip():
        return Fidelity()

    name = _cache_name(description, lean_code)
    cached = proof_cache.load_json(name)
    if cached is not None:
        return Fidelity(**cached)

    translation = back_translate(lean_code)
    if not translation:
        return Fidelity()

    agrees, reason = judge(description, translation)
    result = Fidelity(
        verdict=OK if agrees else DIVERGES,
        back_translation=translation,
        reason=reason,
    )
    proof_cache.save_json(name, result.__dict__)
    return result


def annotate(results, run) -> int:
    """Check every verified property and record the outcome on it. Returns divergences."""
    verified = [r for r in results if r.status == "verified" and r.lean_code]
    if not verified:
        return 0

    log(_log, "VERIFY", f"Checking formalization fidelity of {len(verified)} verified propert(ies)...")

    def _one(result):
        try:
            return result, check(result.description, result.lean_code)
        except BackendUnavailable:
            raise
        except Exception as e:
            log(_log, "ERROR", f"{result.property_id} fidelity check failed: {type(e).__name__}: {e}")
            return result, Fidelity()

    diverged = 0
    for result, fidelity in run(_one, verified):
        result.fidelity = fidelity.verdict
        result.back_translation = fidelity.back_translation
        result.fidelity_reason = fidelity.reason
        if fidelity.verdict == DIVERGES:
            diverged += 1
            log(_log, "FAIL", f"{result.property_id} ⚠ theorem may not match the property — {fidelity.reason}")
    return diverged
