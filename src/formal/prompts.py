"""The text formal serves, kept beside the code rather than inside it.

Nothing here is executed: formal does not call a model. These files are the
accumulated guidance for the three judgements it cannot make for you, rendered by
guide.py and reachable at GET /guide/{topic}.

They live as files because they change on someone else's schedule. Lean renames a
diagnostic, Mathlib moves a lemma, and the fix is an edit to prose — which should
not mean touching Python, and should read as a diff of what was actually said.
"""

from functools import cache
from pathlib import Path

GUIDANCE_DIR = Path(__file__).resolve().parent / "guidance"


@cache
def _read(name: str) -> str:
    """The file holds the text plus one trailing newline, so it ends cleanly on disk.

    That newline is removed rather than stripped: some guidance ends mid-sentence and
    some ends with a blank line, and both must survive a round trip byte for byte.
    """
    return (GUIDANCE_DIR / f"{name}.md").read_text()[:-1]


def names() -> list[str]:
    """Every piece of guidance on disk, by its upper-case name."""
    return sorted(p.stem.upper() for p in GUIDANCE_DIR.glob("*.md"))


def __getattr__(name: str) -> str:
    """Serve NAME from guidance/name.md, so callers read prompts.NAME as before."""
    if name.isupper():
        try:
            return _read(name.lower())
        except FileNotFoundError:
            raise AttributeError(f"no guidance file for {name}") from None
    raise AttributeError(name)
