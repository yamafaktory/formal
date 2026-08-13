"""Match a Lean diagnostic to the advice for it.

The advice used to be a 434-line `if ... in data` chain inside `lean_verifier`
— a third of that module and the largest single thing a rewrite has to
reproduce. Almost all of it was text. `guidance/hints.toml` now holds the rules
in the order they are tried, and this module is only the matcher.

Two consequences worth keeping in mind when editing the table. Order is the
semantics: `omega_on_a_string_literal` has to be tried before
`omega_beyond_linear_arithmetic` or the general answer swallows the specific
one, and `tests/test_hint_corpus.py` fails when it does. And a rule that
produces nothing — a handler whose pattern did not match — is not a match at
all, so the search continues with the next sibling and then the parent's own
advice. That is what let the old chain fall through a nested `if`.
"""

import re
import tomllib
from collections.abc import Callable
from functools import cache
from pathlib import Path

DATA = Path(__file__).parent / "guidance" / "hints.toml"
SCHEMA_VERSION = 1

Rule = dict
Config = dict


class HintTableError(RuntimeError):
    """The hint table cannot be trusted to answer anything."""


def _fill(template: str, **values: str) -> str:
    for key, value in values.items():
        template = template.replace("{" + key + "}", value)
    return template


def _known_rename(data: str, config: Config) -> str | None:
    found = re.search(r"[Uu]nknown (?:identifier|constant) [`']([A-Za-z_.][A-Za-z0-9_.']*)[`']", data)
    if found is None:
        return None
    replacement = config["renames"].get(found.group(1))
    if replacement is None:
        return None
    return _fill(config["template"], name=found.group(1), replacement=replacement)


def _local_hypothesis(data: str, config: Config) -> str | None:
    found = re.search(r"[Uu]nknown identifier [`']((?:h|ih)[a-z]{0,4}[0-9']*)[`']", data)
    if found is None:
        return None
    hint = _fill(config["template"], name=found.group(1))
    if "split_ifs" in data:
        hint += config["split_ifs_suffix"]
    return hint


def _option_inner_type(data: str, config: Config) -> str | None:
    found = re.search(r"has type\s+Option (\S+)", data)
    needed = re.search(r"expected to have type\s+Option (\S+)", data)
    if not found or not needed or found.group(1) == needed.group(1):
        return None
    return _fill(config["template"], found=found.group(1), needed=needed.group(1))


def _hypothesis_is_function(data: str, config: Config) -> str | None:
    named = re.search(r"The argument\s+(\w+)\s+has type", data)
    arrow = re.search(r"has type\s+(.+?)\s+→", data)
    return _fill(
        config["template"],
        name=named.group(1) if named else config["default_name"],
        required=arrow.group(1).strip() if arrow else config["default_required"],
    )


def _function_expected_lemma(data: str, config: Config) -> str | None:
    named = re.search(r"Function expected at\s+(\S+)", data)
    return _fill(config["template"], name=named.group(1) if named else config["default_name"])


def _tactic_failed(data: str, config: Config) -> str | None:
    found = re.search(r"[Tt]actic `([^`]+)` failed", data)
    if found is None:
        return None
    name = found.group(1)
    specific = config["tactics"].get(name)
    return _fill(config["template"], name=name) + (f" {specific}" if specific else "") + config["suffix"]


HANDLERS: dict[str, Callable[[str, Config], str | None]] = {
    "known_rename": _known_rename,
    "local_hypothesis": _local_hypothesis,
    "option_inner_type": _option_inner_type,
    "hypothesis_is_function": _hypothesis_is_function,
    "function_expected_lemma": _function_expected_lemma,
    "tactic_failed": _tactic_failed,
}


def _validate(table: dict) -> None:
    version = table.get("version")
    if version != SCHEMA_VERSION:
        raise HintTableError(f"{DATA} is version {version}, this formal understands {SCHEMA_VERSION}")
    if not table.get("fallback"):
        raise HintTableError(f"{DATA} has no fallback, so an unrecognised error would get no answer")

    seen: set[str] = set()

    def walk(rules: list[Rule], path: str) -> None:
        for rule in rules:
            rule_id = f"{path}{rule.get('id', '?')}"
            if rule_id in seen:
                raise HintTableError(f"{DATA}: duplicate rule id {rule_id}")
            seen.add(rule_id)
            answers = ("hint" in rule) + ("hint_ref" in rule) + ("handler" in rule)
            if answers > 1:
                raise HintTableError(f"{DATA}: {rule_id} gives more than one answer")
            if not answers and not rule.get("sub"):
                raise HintTableError(f"{DATA}: {rule_id} can match but has no answer")
            if "hint_ref" in rule and rule["hint_ref"] not in table.get("text", {}):
                raise HintTableError(f"{DATA}: {rule_id} refers to unknown text {rule['hint_ref']}")
            if "handler" in rule:
                if rule["handler"] not in HANDLERS:
                    raise HintTableError(f"{DATA}: {rule_id} names unknown handler {rule['handler']}")
                if rule["handler"] not in table.get("handler", {}):
                    raise HintTableError(f"{DATA}: no configuration for handler {rule['handler']}")
            walk(rule.get("sub", []), f"{rule_id}/")

    walk(table.get("rule", []), "")
    if not seen:
        raise HintTableError(f"{DATA} lists no rules")


@cache
def table() -> dict:
    try:
        loaded = tomllib.loads(DATA.read_text())
    except FileNotFoundError:
        raise HintTableError(f"no hint table at {DATA}") from None
    except tomllib.TOMLDecodeError as e:
        raise HintTableError(f"{DATA} is not valid TOML: {e}") from None
    _validate(loaded)
    return loaded


def _matches(rule: Rule, data: str) -> bool:
    if "equals" in rule:
        return data == rule["equals"]
    subject = data.lower() if rule.get("lower") else data
    if any(term not in subject for term in rule.get("all", ())):
        return False
    groups = rule.get("any")
    return not groups or any(all(term in subject for term in group) for group in groups)


def _answer(rule: Rule, data: str, loaded: dict) -> str | None:
    for sub in rule.get("sub", ()):
        if _matches(sub, data):
            hint = _answer(sub, data, loaded)
            if hint is not None:
                return hint
    if "handler" in rule:
        return HANDLERS[rule["handler"]](data, loaded["handler"][rule["handler"]])
    if "hint_ref" in rule:
        return loaded["text"][rule["hint_ref"]]
    return rule.get("hint")


def hint_for(data: str) -> str:
    loaded = table()
    for rule in loaded["rule"]:
        if _matches(rule, data) and (hint := _answer(rule, data, loaded)) is not None:
            return hint
    return loaded["fallback"]
