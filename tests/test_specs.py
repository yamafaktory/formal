"""Tests for checked-in property specs.

Two independent extraction runs over one function agreed on the wording of none
of their properties, so specs derived fresh each run can never hit the cache.
Writing them down fixes that, and introduces the one risk worth testing hardest:
a spec outliving the code it describes.
"""

import json

import pytest

from formal import specs

FUNCTION = 'def fmt_elapsed(seconds):\n    if seconds < 60:\n        return f"{seconds:.1f}s"\n    return "long"'


def _entry(**overrides):
    base = {
        "id": "fmt_elapsed/bound",
        "function": "fmt_elapsed",
        "kind": "bound",
        "formal": "forall x, 0 <= x -> fmt_elapsed x != []",
        "description": "the result is never empty",
        "assumptions": ["strings modelled as List Char"],
    }
    return {**base, **overrides}


def _write(tmp_path, entries, version=specs.SPEC_VERSION, source=FUNCTION):
    if source is not None:
        (tmp_path / "mod.py").write_text(f"import os\n\n\n{source}\n\n\ndef other():\n    return 1\n")
    path = tmp_path / "formal.properties.json"
    path.write_text(json.dumps({"version": version, "properties": entries}))
    return path


class TestLoading:
    def test_a_valid_file_yields_its_properties(self, tmp_path):
        loaded = specs.load(_write(tmp_path, [_entry(), _entry(id="fmt_elapsed/format")]))
        assert [s.id for s in loaded.specs] == ["fmt_elapsed/bound", "fmt_elapsed/format"]
        assert loaded.stale_ids == []

    def test_fields_survive_the_round_trip(self, tmp_path):
        loaded = specs.load(_write(tmp_path, [_entry()]))
        spec = loaded.specs[0]
        assert spec.kind == "bound"
        assert spec.formal == "forall x, 0 <= x -> fmt_elapsed x != []"
        assert spec.assumptions == ["strings modelled as List Char"]

    def test_a_relative_path_is_refused(self, tmp_path):
        """The server resolves it, and its working directory is not the caller's."""
        with pytest.raises(specs.SpecError, match="absolute"):
            specs.load("formal.properties.json")

    def test_a_missing_file_is_reported(self, tmp_path):
        with pytest.raises(specs.SpecError, match="no spec file"):
            specs.load(tmp_path / "absent.json")

    def test_malformed_json_is_reported(self, tmp_path):
        path = tmp_path / "formal.properties.json"
        path.write_text("{not json")
        with pytest.raises(specs.SpecError, match="not valid JSON"):
            specs.load(path)

    def test_a_future_version_is_refused(self, tmp_path):
        """Better to stop than to read fields that may have changed meaning."""
        with pytest.raises(specs.SpecError, match="version"):
            specs.load(_write(tmp_path, [_entry()], version=99))

    def test_an_empty_property_list_is_refused(self, tmp_path):
        with pytest.raises(specs.SpecError, match="no properties"):
            specs.load(_write(tmp_path, []))

    def test_a_missing_required_field_is_named(self, tmp_path):
        with pytest.raises(specs.SpecError, match="formal"):
            specs.load(_write(tmp_path, [_entry(formal="  ")]))

    def test_duplicate_ids_are_refused(self, tmp_path):
        """Two properties under one id would share a verdict and a cache entry."""
        with pytest.raises(specs.SpecError, match="duplicate"):
            specs.load(_write(tmp_path, [_entry(), _entry()]))


class TestStaleness:
    def test_a_spec_matching_its_source_is_live(self, tmp_path):
        path = _write(tmp_path, [_entry(source_file="mod.py", function_code=FUNCTION)])
        loaded = specs.load(path)
        assert [s.id for s in loaded.specs] == ["fmt_elapsed/bound"]
        assert loaded.stale_ids == []

    def test_a_spec_whose_source_changed_is_stale(self, tmp_path):
        path = _write(tmp_path, [_entry(source_file="mod.py", function_code=FUNCTION)])
        (tmp_path / "mod.py").write_text("def fmt_elapsed(seconds):\n    return 'rewritten'\n")
        loaded = specs.load(path)
        assert loaded.specs == []
        assert loaded.stale_ids == ["fmt_elapsed/bound"]

    def test_reindenting_the_file_does_not_make_a_spec_stale(self, tmp_path):
        """Trailing whitespace is not a change to the code."""
        path = _write(tmp_path, [_entry(source_file="mod.py", function_code=FUNCTION)])
        (tmp_path / "mod.py").write_text((tmp_path / "mod.py").read_text().replace("\n", "   \n"))
        assert specs.load(path).stale_ids == []

    def test_a_vanished_source_file_is_stale(self, tmp_path):
        path = _write(tmp_path, [_entry(source_file="gone.py", function_code=FUNCTION)])
        assert specs.load(path).stale_ids == ["fmt_elapsed/bound"]

    def test_a_spec_without_a_source_reference_cannot_go_stale(self, tmp_path):
        """Nothing was recorded to compare against, so nothing can be claimed."""
        path = _write(tmp_path, [_entry()])
        assert specs.load(path).stale_ids == []

    def test_only_the_changed_property_goes_stale(self, tmp_path):
        entries = [
            _entry(id="a", source_file="mod.py", function_code=FUNCTION),
            _entry(id="b", source_file="mod.py", function_code="def other():\n    return 1"),
        ]
        (tmp_path / "mod.py").write_text("def other():\n    return 1\n")
        path = tmp_path / "formal.properties.json"
        path.write_text(json.dumps({"version": 1, "properties": entries}))
        loaded = specs.load(path)
        assert loaded.stale_ids == ["a"]
        assert [s.id for s in loaded.specs] == ["b"]

    def test_root_overrides_where_sources_are_looked_up(self, tmp_path):
        code_root = tmp_path / "repo"
        code_root.mkdir()
        (code_root / "mod.py").write_text(FUNCTION + "\n")
        elsewhere = tmp_path / "specs"
        elsewhere.mkdir()
        path = elsewhere / "formal.properties.json"
        path.write_text(
            json.dumps(
                {"version": 1, "properties": [_entry(source_file="mod.py", function_code=FUNCTION)]},
            )
        )
        assert specs.load(path).stale_ids == ["fmt_elapsed/bound"]
        assert specs.load(path, root=code_root).stale_ids == []


class TestReadProofs:
    """Every caller so far wrote a script to load .lean files and escape them into JSON.
    One kept its proofs inside a Python module rather than as .lean files at all, because
    that is what submitting them required."""

    def test_proofs_are_read_from_disk(self, tmp_path):
        (tmp_path / "a.lean").write_text("import Mathlib\ntheorem a : True := trivial")
        (tmp_path / "b.lean").write_text("theorem b : True := trivial")
        proofs = specs.read_proofs({"one": str(tmp_path / "a.lean"), "two": str(tmp_path / "b.lean")})
        assert proofs["one"].startswith("import Mathlib")
        assert proofs["two"] == "theorem b : True := trivial"

    def test_a_relative_path_is_refused(self):
        with pytest.raises(specs.SpecError, match="absolute"):
            specs.read_proofs({"one": "proofs/a.lean"})

    def test_a_missing_file_names_the_property(self, tmp_path):
        with pytest.raises(specs.SpecError, match="one"):
            specs.read_proofs({"one": str(tmp_path / "absent.lean")})

    def test_nothing_to_read_is_nothing(self):
        assert specs.read_proofs({}) == {}
