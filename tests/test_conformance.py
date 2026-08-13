"""The conformance suite, run against this implementation.

`tests/conformance/suite.py` is the contract and knows nothing about Python. This
file is one of its two callers; the other is `python -m tests.conformance.run`
pointed at any server that claims to be formal.

Keeping it in the normal test run is the point. A golden file nobody executes
records what the server did on the day it was written, not what it does now.
"""

import json

import pytest
from fastapi.testclient import TestClient

from formal import api
from formal import session as sessions
from tests.conformance import suite


@pytest.fixture(scope="module")
def recorded(tmp_path_factory):
    sessions._SESSIONS.clear()
    client = TestClient(api.app)

    def request(method: str, path: str, body: dict | None):
        response = client.request(method, path, json=body)
        try:
            return response.status_code, response.json()
        except ValueError:
            return response.status_code, response.text

    return suite.run(request, tmp_path_factory.mktemp("conformance"))


class TestConformance:
    def test_the_server_answers_what_the_golden_file_says(self, recorded):
        problems = suite.differences(recorded, suite.load_golden())
        assert problems == {}, "\n".join(f"{name}: {'; '.join(found)}" for name, found in problems.items())

    def test_every_step_was_reached(self, recorded):
        assert set(recorded) == set(suite.load_golden())


class TestTheSuiteIsWorthRunning:
    """A suite that pins nothing passes everything."""

    def test_it_covers_both_success_and_refusal(self, recorded):
        codes = {entry["status"] for entry in recorded.values()}
        assert {200, 400, 404} <= codes

    def test_it_pins_the_bodies_formal_writes(self, recorded):
        assert all("body" in entry for entry in recorded.values() if entry["status"] != 422)

    def test_the_golden_file_is_committed_and_parses(self):
        assert isinstance(json.loads(suite.GOLDEN.read_text()), dict)


class TestComparisonCatchesDivergence:
    """The comparison is the whole suite. If it cannot fail, nothing else matters."""

    GOLDEN = {"a": {"status": 200, "body": {"status": "ok"}}}

    def test_a_changed_status_is_reported(self):
        recorded = {"a": {"status": 500, "body": {"status": "ok"}}}
        assert "status 500, expected 200" in suite.differences(recorded, self.GOLDEN)["a"][0]

    def test_a_changed_body_is_reported(self):
        recorded = {"a": {"status": 200, "body": {"status": "OK"}}}
        assert suite.differences(recorded, self.GOLDEN)["a"]

    def test_a_step_the_server_never_answered_is_reported(self):
        assert suite.differences({}, self.GOLDEN) == {"a": ["not exercised"]}

    def test_a_step_missing_from_the_golden_file_is_reported(self):
        recorded = {**self.GOLDEN, "b": {"status": 200, "body": {}}}
        assert suite.differences(recorded, self.GOLDEN) == {"b": ["not in the golden file"]}

    def test_agreement_reports_nothing(self):
        assert suite.differences(dict(self.GOLDEN), self.GOLDEN) == {}

    def test_long_strings_are_compared_by_digest_not_ignored(self):
        replacements: dict[str, str] = {}
        one = suite._normalise("x" * (suite.DIGEST_OVER + 1), replacements)
        other = suite._normalise("y" * (suite.DIGEST_OVER + 1), replacements)
        assert one != other and one["chars"] == other["chars"]
