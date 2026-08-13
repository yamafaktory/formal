"""What formal's HTTP surface must do, stated without reference to Python.

Nothing here imports `formal`. The suite drives a server through a `request`
callable and records what came back; `golden/responses.json` says what that
should be. A reimplementation passes by serving the same answers, which is the
only definition of "same behaviour" that survives changing languages.

Two rules about what gets pinned. Status codes are pinned everywhere, including
on the paths that only exist to be refused — half of an API is what it rejects.
Response bodies are pinned where formal writes them and left alone where the web
framework writes them: a 422 body is FastAPI's shape, not formal's contract, so
the suite checks the code and stops there.

Long strings are recorded as a digest rather than inline. The guidance texts are
version-controlled next to the server that serves them, so a diff there is
already reviewable, and 30KB of prose inside the golden file would make every
other line of it unreadable.
"""

import hashlib
import json
from collections.abc import Callable
from pathlib import Path

GOLDEN = Path(__file__).parent / "golden" / "responses.json"
DIGEST_OVER = 400

Request = Callable[[str, str, dict | None], tuple[int, object]]

PROPERTIES = [
    {
        "id": "reverse/involutive",
        "description": "reversing twice returns the original list",
        "kind": "invariant",
        "function": "reverse",
        "function_code": "def reverse(xs): return xs[::-1]",
        "formal": "forall xs, reverse (reverse xs) = xs",
        "preconditions": [],
        "assumptions": [],
    },
    {
        "id": "reverse/length",
        "description": "reversing preserves length",
        "kind": "invariant",
        "function": "reverse",
        "function_code": "def reverse(xs): return xs[::-1]",
        "formal": "forall xs, (reverse xs).length = xs.length",
        "preconditions": [],
        "assumptions": [],
    },
]

SPEC_FILE = {
    "version": 1,
    "properties": [
        {
            "id": "identity/fixed",
            "description": "the identity function returns its argument",
            "kind": "invariant",
            "function": "identity",
            "function_code": "def identity(x): return x",
            "source_file": "source.py",
            "formal": "forall x, identity x = x",
        },
        {
            "id": "gone/stale",
            "description": "written against source that has since changed",
            "kind": "invariant",
            "function": "gone",
            "function_code": "def gone(x): return x + 1",
            "source_file": "source.py",
            "formal": "forall x, gone x > x",
        },
    ],
}

SOURCE_FILE = "def identity(x): return x\n"


def _digest(text: str) -> dict:
    return {"sha256": hashlib.sha256(text.encode()).hexdigest(), "chars": len(text)}


def _normalise(value, replacements: dict[str, str]):
    """Strip out what legitimately differs between two runs of the same server."""
    if isinstance(value, str):
        for original, placeholder in replacements.items():
            value = value.replace(original, placeholder)
        return _digest(value) if len(value) > DIGEST_OVER else value
    if isinstance(value, list):
        return [_normalise(item, replacements) for item in value]
    if isinstance(value, dict):
        return {key: _normalise(item, replacements) for key, item in value.items()}
    return value


def run(request: Request, workspace: Path) -> dict:
    """Drive one server through the whole surface and return what it answered."""
    (workspace / "source.py").write_text(SOURCE_FILE)
    spec_path = workspace / "conformance.properties.json"
    spec_path.write_text(json.dumps(SPEC_FILE))
    missing_path = workspace / "absent.properties.json"

    recorded: dict[str, dict] = {}
    replacements = {str(workspace): "<workspace>"}

    def step(name: str, method: str, path: str, body: dict | None = None) -> object:
        status, payload = request(method, path, body)
        entry: dict = {"status": status}
        if status != 422:
            entry["body"] = _normalise(payload, replacements)
        recorded[name] = entry
        return payload

    def open_session(name: str, body: dict, placeholder: str) -> str:
        """Register the id as a placeholder before recording, since it is in the body."""
        status, payload = request("POST", "/session", body)
        session_id = payload.get("session_id", "") if isinstance(payload, dict) else ""
        if session_id:
            replacements[session_id] = placeholder
        recorded[name] = {"status": status, "body": _normalise(payload, replacements)}
        return session_id

    step("health", "GET", "/health")
    step("guide_index", "GET", "/guide")
    for topic in ("extract", "formalize", "tactics"):
        step(f"guide_{topic}", "GET", f"/guide/{topic}")
    step("guide_unknown_topic", "GET", "/guide/no-such-topic")

    session_id = open_session("session_open", {"properties": PROPERTIES}, "<session>")

    step("session_read", "GET", f"/session/{session_id}")
    step("session_read_unknown", "GET", "/session/0000000000000000")

    step("session_open_with_neither", "POST", "/session", {})
    step("session_open_with_both", "POST", "/session", {"properties": PROPERTIES, "spec_file": str(spec_path)})
    step("session_open_duplicate_ids", "POST", "/session", {"properties": [PROPERTIES[0], PROPERTIES[0]]})
    step("session_open_relative_spec", "POST", "/session", {"spec_file": "relative.properties.json"})
    step("session_open_absent_spec", "POST", "/session", {"spec_file": str(missing_path)})

    spec_session = open_session("session_open_from_spec", {"spec_file": str(spec_path)}, "<spec-session>")

    check = f"/session/{session_id}/check"
    step("check_with_neither", "POST", check, {})
    step("check_with_both", "POST", check, {"proofs": {"reverse/involutive": "x"}, "proof_files": {"a": "/b.lean"}})
    step("check_unknown_property", "POST", check, {"proofs": {"not/registered": "theorem t : True := trivial"}})
    step("check_relative_proof_file", "POST", check, {"proof_files": {"reverse/involutive": "proof.lean"}})
    step("check_on_unknown_session", "POST", "/session/0000000000000000/check", {"proofs": {"a": "b"}})

    step("proof_unregistered", "GET", f"/session/{session_id}/proof/not/registered")
    step("proof_not_yet_accepted", "GET", f"/session/{session_id}/proof/reverse/involutive")
    step("proof_on_unknown_session", "GET", "/session/0000000000000000/proof/reverse/involutive")

    step("session_close", "DELETE", f"/session/{session_id}")
    step("session_close_again", "DELETE", f"/session/{session_id}")
    step("session_read_after_close", "GET", f"/session/{session_id}")
    step("session_close_spec_session", "DELETE", f"/session/{spec_session}")

    return recorded


def load_golden() -> dict:
    return json.loads(GOLDEN.read_text())


def differences(recorded: dict, golden: dict) -> dict[str, list[str]]:
    """Every disagreement, by step — a port wants the whole list, not the first one."""
    problems: dict[str, list[str]] = {}
    for name in sorted(set(golden) - set(recorded)):
        problems[name] = ["not exercised"]
    for name in sorted(set(recorded) - set(golden)):
        problems[name] = ["not in the golden file"]
    for name in sorted(set(recorded) & set(golden)):
        got, want = recorded[name], golden[name]
        found = []
        if got.get("status") != want.get("status"):
            found.append(f"status {got.get('status')}, expected {want.get('status')}")
        if got.get("body") != want.get("body"):
            got_body = json.dumps(got.get("body"), sort_keys=True, ensure_ascii=False)
            want_body = json.dumps(want.get("body"), sort_keys=True, ensure_ascii=False)
            found.append(f"body\n     got {got_body}\n    want {want_body}")
        if found:
            problems[name] = found
    return problems
