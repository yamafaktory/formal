"""Tests for the HTTP surface — a session must reject anything it cannot
attribute to a registered property."""

import json
from unittest.mock import patch

import pytest
from fastapi.testclient import TestClient

from formal import api
from formal import session as sessions
from formal.checker import Outcome


@pytest.fixture
def client(monkeypatch):
    monkeypatch.setattr(sessions, "_SESSIONS", {})
    return TestClient(api.app)


def _props(*ids):
    return {
        "properties": [
            {"id": pid, "description": f"{pid} holds", "kind": "bound", "function": "f", "function_code": "def f(): 0"}
            for pid in ids
        ]
    }


class TestSessionEndpoints:
    def test_opening_reports_what_needs_proving(self, client):
        body = client.post("/session", json=_props("p1", "p2")).json()
        assert body["work"] == ["p1", "p2"]
        assert body["cached"] == []
        assert not body["complete"]

    def test_an_empty_property_list_is_rejected(self, client):
        assert client.post("/session", json={"properties": []}).status_code == 400

    def test_duplicate_ids_are_rejected(self, client):
        """Two properties under one id would silently share a verdict and a cache key."""
        response = client.post("/session", json=_props("p1", "p1"))
        assert response.status_code == 400
        assert "p1" in response.json()["detail"]

    def test_checking_returns_verdicts_and_what_remains(self, client):
        sid = client.post("/session", json=_props("p1", "p2")).json()["session_id"]
        outcomes = [
            Outcome(id="p1", status="verified", lean_code="ok"),
            Outcome(id="p2", status="failed", lean_code="bad", error="no goals", line=3, hint="drop a tactic"),
        ]
        with patch("formal.session.check_batch", return_value=outcomes):
            body = client.post(f"/session/{sid}/check", json={"proofs": {"p1": "a", "p2": "b"}}).json()

        assert body["verified"] == ["p1"]
        assert body["failed"] == [{"id": "p2", "error": "no goals", "line": 3, "col": None, "hint": "drop a tactic"}]
        assert body["remaining"] == ["p2"]
        assert not body["complete"]

    def test_a_proof_for_an_unregistered_id_is_rejected(self, client):
        sid = client.post("/session", json=_props("p1")).json()["session_id"]
        assert client.post(f"/session/{sid}/check", json={"proofs": {"zz": "x"}}).status_code == 400

    def test_an_unknown_session_is_not_found(self, client):
        assert client.get("/session/nope").status_code == 404
        assert client.post("/session/nope/check", json={"proofs": {}}).status_code == 404
        assert client.delete("/session/nope").status_code == 404

    def test_a_session_can_be_closed(self, client):
        sid = client.post("/session", json=_props("p1")).json()["session_id"]
        assert client.delete(f"/session/{sid}").status_code == 200
        assert client.get(f"/session/{sid}").status_code == 404


class TestSpecFileSessions:
    def _spec_file(self, tmp_path, entries, source="def f():\n    return 1"):
        (tmp_path / "mod.py").write_text(source + "\n")
        path = tmp_path / "formal.properties.json"
        path.write_text(json.dumps({"version": 1, "properties": entries}))
        return str(path)

    def _entry(self, **over):
        base = {"id": "f/bound", "function": "f", "kind": "bound", "formal": "forall x, f x = 1"}
        return {**base, **over}

    def test_a_session_can_be_opened_from_a_spec_file(self, client, tmp_path):
        path = self._spec_file(tmp_path, [self._entry(), self._entry(id="f/identity")])
        body = client.post("/session", json={"spec_file": path}).json()
        assert body["work"] == ["f/bound", "f/identity"]
        assert body["stale"] == []

    def test_a_spec_whose_source_moved_is_reported_not_proved(self, client, tmp_path):
        path = self._spec_file(tmp_path, [self._entry(source_file="mod.py", function_code="def f():\n    return 1")])
        (tmp_path / "mod.py").write_text("def f():\n    return 2\n")
        body = client.post("/session", json={"spec_file": path}).json()
        assert body["stale"] == ["f/bound"]
        assert body["work"] == []
        assert not body["complete"]

    def test_a_broken_spec_file_is_a_client_error(self, client, tmp_path):
        path = tmp_path / "formal.properties.json"
        path.write_text('{"version": 1, "properties": []}')
        response = client.post("/session", json={"spec_file": str(path)})
        assert response.status_code == 400
        assert "no properties" in response.json()["detail"]

    def test_a_missing_spec_file_is_a_client_error(self, client, tmp_path):
        response = client.post("/session", json={"spec_file": str(tmp_path / "absent.json")})
        assert response.status_code == 400

    def test_properties_and_spec_file_together_are_refused(self, client, tmp_path):
        path = self._spec_file(tmp_path, [self._entry()])
        response = client.post("/session", json={"spec_file": path, **_props("p1")})
        assert response.status_code == 400

    def test_neither_properties_nor_spec_file_is_refused(self, client):
        assert client.post("/session", json={}).status_code == 400


class TestVersion:
    def test_the_api_reports_the_installed_version(self):
        """It was hardcoded, and said 2.0.0 while the package said 1.0.0."""
        import pathlib
        import re

        pyproject = (pathlib.Path(__file__).parent.parent / "pyproject.toml").read_text()
        declared = re.search(r'^version = "([^"]+)"', pyproject, re.M).group(1)
        assert api.app.version == declared


class TestProofRetrieval:
    def _session(self, client):
        return client.post("/session", json=_props("p1")).json()["session_id"]

    def test_a_recovered_proof_is_flagged_in_the_response(self, client):
        sid = self._session(client)
        outcome = Outcome(id="p1", status="verified", lean_code="accepted", checked=True, recovered=True)
        with patch("formal.session.check_batch", return_value=[outcome]):
            body = client.post(f"/session/{sid}/check", json={"proofs": {"p1": "sent"}}).json()

        assert body["verified"] == ["p1"]
        assert body["recovered"] == ["p1"]

    def test_the_accepted_proof_is_retrievable(self, client):
        sid = self._session(client)
        outcome = Outcome(id="p1", status="verified", lean_code="the accepted proof", checked=True, recovered=True)
        with patch("formal.session.check_batch", return_value=[outcome]):
            client.post(f"/session/{sid}/check", json={"proofs": {"p1": "sent"}})

        body = client.get(f"/session/{sid}/proof/p1").json()
        assert body == {"id": "p1", "origin": "recovered", "lean_code": "the accepted proof"}

    def test_nothing_accepted_yet_is_not_found(self, client):
        sid = self._session(client)
        assert client.get(f"/session/{sid}/proof/p1").status_code == 404

    def test_an_unregistered_id_is_not_found(self, client):
        sid = self._session(client)
        assert client.get(f"/session/{sid}/proof/nope").status_code == 404
