"""Tests for api._save — distinct labels must never share a result file."""

import json

import pytest

from formal import api


@pytest.fixture
def results_dir(tmp_path, monkeypatch):
    monkeypatch.setattr(api, "RESULTS_DIR", tmp_path)
    return tmp_path


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
