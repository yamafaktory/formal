"""Property specs the repository owns, rather than ones an LLM re-invents.

Two independent extraction runs over one function produced six and seven
properties, agreed on the wording of none of them, and disagreed on the direction
of one — so nothing derived fresh each run can key a cache, and no amount of
string normalisation closes that. Writing the specs down once removes the
question: the same bytes every run, and a diff when someone changes them.

It also makes the claim reviewable. A verification tool whose properties are
re-invented per run cannot tell you what it checked last week.

The risk a checked-in spec introduces is that the code moves and the property
does not, so a stale proof answers a question nobody is asking any more. Each
spec carries the function source it was written against, and a spec whose source
has since changed is reported rather than proved.
"""

import json
from dataclasses import dataclass, field
from pathlib import Path

from .proof_cache import normalise_code
from .session import PropertySpec

SPEC_VERSION = 1
REQUIRED = ("id", "function", "kind", "formal")


class SpecError(ValueError):
    """The spec file cannot be trusted to describe anything."""


@dataclass
class LoadedSpec:
    spec: PropertySpec
    source_file: str
    stale: bool = False


@dataclass
class SpecFile:
    path: Path
    live: list[LoadedSpec] = field(default_factory=list)
    stale: list[LoadedSpec] = field(default_factory=list)

    @property
    def specs(self) -> list[PropertySpec]:
        return [entry.spec for entry in self.live]

    @property
    def stale_ids(self) -> list[str]:
        return [entry.spec.id for entry in self.stale]


def _read(path: Path) -> list[dict]:
    try:
        payload = json.loads(path.read_text())
    except FileNotFoundError:
        raise SpecError(f"no spec file at {path}") from None
    except json.JSONDecodeError as e:
        raise SpecError(f"{path} is not valid JSON: {e}") from None

    if not isinstance(payload, dict) or "properties" not in payload:
        raise SpecError(f"{path} must be an object with a 'properties' list")
    version = payload.get("version", SPEC_VERSION)
    if version != SPEC_VERSION:
        raise SpecError(f"{path} is version {version}, this formal understands {SPEC_VERSION}")
    entries = payload["properties"]
    if not isinstance(entries, list) or not entries:
        raise SpecError(f"{path} lists no properties")
    return entries


def _validate(entries: list[dict], path: Path) -> None:
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            raise SpecError(f"{path}: property {index} is not an object")
        missing = [f for f in REQUIRED if not str(entry.get(f, "")).strip()]
        if missing:
            raise SpecError(f"{path}: property {index} is missing {', '.join(missing)}")

    ids = [e["id"] for e in entries]
    duplicates = sorted({i for i in ids if ids.count(i) > 1})
    if duplicates:
        raise SpecError(f"{path}: duplicate property ids: {', '.join(duplicates)}")


def _is_stale(entry: dict, root: Path) -> bool:
    """Whether the source this property was written against still says the same thing.

    Compared as normalised text rather than parsed, so it holds for every language
    formal accepts. A spec with no recorded source cannot go stale — there is
    nothing to compare it against.
    """
    source_file, function_code = entry.get("source_file", ""), entry.get("function_code", "")
    if not source_file or not function_code:
        return False
    try:
        current = (root / source_file).read_text()
    except OSError:
        return True
    return normalise_code(function_code) not in normalise_code(current)


def load(path: str | Path, root: str | Path | None = None) -> SpecFile:
    """Read a spec file, separating properties still describing their source from those that are not."""
    path = Path(path).expanduser()
    root = Path(root) if root is not None else path.parent
    entries = _read(path)
    _validate(entries, path)

    result = SpecFile(path=path)
    for entry in entries:
        loaded = LoadedSpec(
            spec=PropertySpec(
                id=entry["id"],
                description=entry.get("description", ""),
                kind=entry["kind"],
                function=entry["function"],
                function_code=entry.get("function_code", ""),
                formal=entry["formal"],
                preconditions=list(entry.get("preconditions", [])),
                assumptions=list(entry.get("assumptions", [])),
            ),
            source_file=entry.get("source_file", ""),
            stale=_is_stale(entry, root),
        )
        (result.stale if loaded.stale else result.live).append(loaded)
    return result
