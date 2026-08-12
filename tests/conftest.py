import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))


@pytest.fixture(autouse=True)
def isolated_cache(tmp_path, monkeypatch):
    """Point the disk cache at a scratch directory for every test.

    decompose and extract_properties consult it, so without this a test would
    both read another test's entries and write into the real results/cache.
    """
    import formal.proof_cache as proof_cache

    monkeypatch.setattr(proof_cache, "_CACHE_DIR", tmp_path / "cache")
