import sys
from pathlib import Path

# Make the repo root importable as the `formal` package.
# The .py files live directly in /repo/formal/ on disk, mirroring
# how Docker copies them to /app/formal/.
sys.path.insert(0, str(Path(__file__).parent.parent.parent))
