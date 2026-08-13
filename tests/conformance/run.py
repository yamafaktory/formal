"""Run the conformance suite against a server, or record what it answers.

    python -m tests.conformance.run --base-url http://127.0.0.1:8000
    python -m tests.conformance.run --base-url http://127.0.0.1:8000 --update

The server under test must have an empty proof cache, or properties the suite
expects to be unproved will come back cached. Point PROOF_CACHE_DIR at a scratch
directory before starting it.
"""

import argparse
import json
import sys
import tempfile
from pathlib import Path

import httpx2 as httpx

from . import suite


def http_request(base_url: str):
    client = httpx.Client(base_url=base_url, timeout=30.0)

    def request(method: str, path: str, body: dict | None) -> tuple[int, object]:
        response = client.request(method, path, json=body)
        try:
            return response.status_code, response.json()
        except ValueError:
            return response.status_code, response.text

    return request


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base-url", required=True)
    parser.add_argument("--update", action="store_true", help="rewrite the golden file instead of comparing")
    args = parser.parse_args(argv)

    with tempfile.TemporaryDirectory() as workspace:
        recorded = suite.run(http_request(args.base_url), Path(workspace))

    if args.update:
        suite.GOLDEN.parent.mkdir(parents=True, exist_ok=True)
        suite.GOLDEN.write_text(json.dumps(recorded, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
        print(f"recorded {len(recorded)} responses to {suite.GOLDEN}")
        return 0

    problems = suite.differences(recorded, suite.load_golden())
    for name, found in problems.items():
        for problem in found:
            print(f"  {name}: {problem}")
    print(f"{len(recorded) - len(problems)}/{len(recorded)} steps conformant")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
