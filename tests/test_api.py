"""Tests for the HTTP surface: result files must not collide, and a session must
reject anything it cannot attribute to a registered property."""

import json
from unittest.mock import patch

import pytest
from fastapi.testclient import TestClient

from formal import api
from formal import session as sessions
from formal.checker import Outcome


@pytest.fixture
def results_dir(tmp_path, monkeypatch):
    monkeypatch.setattr(api, "RESULTS_DIR", tmp_path)
    return tmp_path


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


def _written(results_dir):
    return sorted(p.name for p in results_dir.glob("*.json"))


class TestSaveCollisions:
    def test_labels_differing_only_in_punctuation_do_not_collide(self, results_dir):
        """Every non-alphanumeric character mapped to _, so a-b and a_b were one file."""
        api._save("feature", "a-b", {"n": 1})
        api._save("feature", "a_b", {"n": 2})
        assert len(_written(results_dir)) == 2

    def test_long_labels_sharing_a_prefix_do_not_collide(self, results_dir):
        shared = "/home/davy/dev/some/deeply/nested/project/src/module"
        api._save("feature", f"{shared}/alpha.py", {"n": 1})
        api._save("feature", f"{shared}/beta.py", {"n": 2})
        assert len(_written(results_dir)) == 2

    def test_the_same_label_reuses_one_file(self, results_dir):
        api._save("feature", "same.py", {"n": 1})
        api._save("feature", "same.py", {"n": 2})
        names = _written(results_dir)
        assert len(names) == 1
        assert json.loads((results_dir / names[0]).read_text()) == {"n": 2}

    def test_different_prefixes_stay_separate(self, results_dir):
        api._save("verify", "x", {"n": 1})
        api._save("feature", "x", {"n": 2})
        assert len(_written(results_dir)) == 2


class TestSaveNaming:
    def test_the_name_stays_readable(self, results_dir):
        api._save("feature", "src/formal/cli.py", {})
        assert _written(results_dir)[0].startswith("feature_src_formal_cli_py_")

    def test_a_very_long_label_is_truncated_but_still_unique(self, results_dir):
        long_a = "x" * 300 + "a"
        long_b = "x" * 300 + "b"
        api._save("feature", long_a, {})
        api._save("feature", long_b, {})
        names = _written(results_dir)
        assert len(names) == 2
        assert all(len(n) < 120 for n in names)

    def test_the_payload_round_trips(self, results_dir):
        api._save("feature", "x.py", {"verified": 3, "total": 4})
        name = _written(results_dir)[0]
        assert json.loads((results_dir / name).read_text()) == {"verified": 3, "total": 4}


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
