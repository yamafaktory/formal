import functools
import importlib.util
import os
import sys
from pathlib import Path

import pytest
from hypothesis import settings

settings.register_profile("bench", max_examples=1000)
settings.load_profile("bench")


@pytest.fixture(scope="session")
def load():
    @functools.cache
    def loaded(file):
        path = Path(os.environ["BENCH_WORK"]) / file
        spec = importlib.util.spec_from_file_location(f"bench_{path.stem}", path)
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        return module

    return loaded
