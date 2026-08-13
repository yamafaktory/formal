"""What formal knows about writing properties, served to whoever is driving it.

The prompts here are the ones the LLM pipeline uses. An agent supplying its own
proofs should work from the same text rather than reinvent it, so this renders
them from prompts.py instead of restating them — one place to edit, and the two
paths cannot drift apart.

Served in stages because it is not small: the index is the workflow and the spec
schema, and each phase's instructions are fetched only when that phase starts.
Handing an agent four thousand tokens of Lean conventions before it has decided
what to prove is the kind of waste this whole design exists to remove.
"""

import re

from . import prompts

PLACEHOLDERS = {
    "language": "<the source language, e.g. Python>",
    "code": "<the full source of the file under test>",
    "feature_summary": "<one sentence on what the file does>",
    "pure_functions": "<the pure functions you identified, with their source>",
    "function_code": "<the source of the function this property is about>",
    "description": "<the property's description field>",
    "formal": "<the property's formal field>",
    "kind": "<the property's kind field>",
    "preconditions": "<the property's preconditions, one per line>",
    "assumptions": "<the property's assumptions, one per line>",
    "error": "<the error field from the failed check>",
    "line": "<the line field>",
    "col": "<the col field>",
    "hint": "<the hint field>",
    "current": "<the proof Lean rejected>",
}

WORKFLOW = [
    "Read the source file you intend to check.",
    "GET /guide/extract, follow it, and identify the pure functions and their properties.",
    "Write those properties to a spec file (see spec_file below), adding source_file and "
    "function_code to each. Commit it: it is reviewable, and identical bytes each run are "
    "what let the proof cache work at all.",
    "POST /session with {'spec_file': '<absolute path>'}. The reply says which properties are "
    "already cached, which need proving, and which are stale. The path must be absolute: the "
    "server resolves it, and its working directory is not yours.",
    "GET /guide/formalize, then write a Lean 4 theorem and proof for each id under 'work'. "
    "GET /guide/tactics too — most first-attempt failures are one of the rules it lists.",
    "POST /session/{session_id}/check with {'proofs': {'<id>': '<lean>'}}.",
    "For each failure, read its error and hint, fix that proof, and resubmit only the ids "
    "that failed — the first submission carries everything, a retry carries only what broke. "
    "Repeat until 'complete' is true.",
]

SESSION_LIFETIME = (
    "A session is in-memory and expires after an idle period (SESSION_TTL_MINUTES, one hour by "
    "default), and it is lost if the server restarts. Once it is gone, POST /session again with "
    "the same spec file: anything already proved comes straight back as a cache hit, so you never "
    "reprove it. A 404 from /session/{id}/check means expired, not wrong — reopen and carry on."
)

WHAT_VERIFIED_MEANS = (
    "A verified id means Lean accepted a proof of that theorem — not necessarily the proof you "
    "sent. Before reporting a failure, formal retries the goal with a fixed tactic chain and then "
    "searches Mathlib for a lemma that closes it, so a proof of yours that did not work may still "
    "come back verified because something else did. The proof that was accepted is what gets "
    "cached."
)

STALE_ADVICE = (
    "A stale id means the function changed since the property was written against it, so the "
    "property may no longer describe anything. Re-read that function, rewrite the property, and "
    "update its function_code in the spec file. Stale properties are never proved."
)

SPEC_FILE = {
    "filename": "formal.properties.json (conventional; any path works)",
    "schema": {
        "version": 1,
        "properties": [
            {
                "id": "required — stable across runs, e.g. 'fmt_elapsed/monotonicity'",
                "function": "required — the function this is about",
                "kind": "required — one of: bound, identity, monotonicity, commutativity, idempotency, invariant",
                "formal": "required — the mathematical statement, e.g. 'forall x, f x <= x'",
                "description": "optional — one line of prose for a human reviewer",
                "preconditions": "optional — list of what must hold on inputs",
                "assumptions": "optional — list of modelling choices made",
                "source_file": "optional but recommended — path, relative to the spec file, "
                "that function_code came from",
                "function_code": "optional but recommended — the function's source, so formal "
                "can tell you when it has changed underneath the property",
            }
        ],
    },
    "notes": [
        "id, function, kind and formal identify the property. The cache key is derived from the "
        "function source, the kind and the formal statement, so those three must stay stable "
        "across runs for a proof to be reused; prose may change freely.",
        "Prose is not in the key, so a cache hit reports the description and assumptions recorded "
        "when the proof was accepted. Read them — if that modelling is not yours, the hit is not "
        "the property you meant.",
    ],
}


def _render(template: str) -> str:
    fields = set(re.findall(r"(?<!\{)\{(\w+)\}(?!\})", template))
    return template.format(**{f: PLACEHOLDERS.get(f, f"<{f}>") for f in fields})


def _extract() -> str:
    return "\n\n".join(
        [
            "## Step 1 — separate pure logic from side effects",
            prompts.DECOMPOSE_SYSTEM.strip(),
            _render(prompts.DECOMPOSE_USER),
            "## Step 2 — identify properties worth proving",
            prompts.PROPERTY_EXTRACTION_SYSTEM.strip(),
            _render(prompts.PROPERTY_EXTRACTION_USER),
            "## Step 3 — write the spec file",
            "Take the properties from step 2, drop any with verifiable=false, and write the rest "
            "to the spec file described by GET /guide. Add source_file and function_code to each. "
            "Choose ids that you would choose again next run — they are how a human reads the diff.",
        ]
    )


def _tactics() -> str:
    return "\n\n".join(
        [
            "## Rules that prevent the common failures",
            prompts.PROOF_GENERATION_SYSTEM.strip(),
            _render(prompts.PROOF_GENERATION_USER),
            "## " + prompts.FINITE_CASE_ANALYSIS.split(chr(10))[0],
            prompts.FINITE_CASE_ANALYSIS.split(chr(10), 1)[1].strip(),
            "## " + prompts.FILTER_AND_PARTITION.split(chr(10))[0],
            prompts.FILTER_AND_PARTITION.split(chr(10), 1)[1].strip(),
            "## When Lean rejects a proof",
            _render(prompts.PROOF_RETRY_USER),
            "The check response gives you the first error, its position, and a hint chosen for "
            "that specific error. Fix that one and resubmit only the ids that failed — a proof "
            "already accepted is never re-checked.",
        ]
    )


def _formalize() -> str:
    return "\n\n".join(
        [
            "## Writing the Lean",
            prompts.AUTOFORMALIZE_SYSTEM.strip(),
            _render(prompts.PROPERTY_FORMALIZE_AND_PROVE_USER),
            "## Submitting",
            "Send every proof for the session in one request: they are checked in a single Lean "
            "invocation, so one request costs one Mathlib import rather than one per proof. Retries "
            "are the exception — resubmit only the ids that failed, since anything already accepted "
            "is never rechecked. A proof that still contains `sorry` is a failure, not partial credit.",
            "Your proofs are concatenated into one file to be checked together, but you do not have "
            "to defend against that. Imports are hoisted and de-duplicated, and each proof is wrapped "
            "in its own namespace, so identical theorem or definition names across proofs cannot "
            "collide. Keep `import Mathlib` at the top of each proof and name things whatever you "
            "like. Reported line numbers are rebased onto the file you submitted, not the batch.",
        ]
    )


TOPICS = {
    "extract": ("how to identify pure functions and the properties worth proving", _extract),
    "formalize": ("Lean 4 conventions for stating and proving a property", _formalize),
    "tactics": ("tactic rules that prevent the common failures, and what to do when Lean rejects a proof", _tactics),
}


def index() -> dict:
    return {
        "workflow": WORKFLOW,
        "spec_file": SPEC_FILE,
        "stale": STALE_ADVICE,
        "sessions": SESSION_LIFETIME,
        "verified": WHAT_VERIFIED_MEANS,
        "topics": {name: summary for name, (summary, _) in TOPICS.items()},
    }


def topic(name: str) -> str:
    if name not in TOPICS:
        raise KeyError(name)
    return TOPICS[name][1]()
