"""Installation and backend configuration, driven by `formal setup`."""

import getpass
import os
import subprocess
from pathlib import Path

from . import sandbox, toolchain
from .paths import FORMAL_HOME, LEAN_PROJECT_DIR

ELAN_INSTALLER = "https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"


def env_file() -> Path:
    return FORMAL_HOME / ".env"


def mathlib_lib() -> Path:
    return LEAN_PROJECT_DIR / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib"


def _say(message: str = "") -> None:
    print(message)


def _ask(prompt: str, default: str = "") -> str:
    try:
        answer = input(prompt).strip()
    except EOFError:
        return default
    return answer or default


def _confirm(prompt: str) -> bool:
    return not _ask(prompt, "y").lower().startswith("n")


def read_env() -> dict[str, str]:
    path = env_file()
    if not path.is_file():
        return {}
    values = {}
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if line and not line.startswith("#") and "=" in line:
            key, _, value = line.partition("=")
            values[key.strip()] = value.strip()
    return values


def write_env(updates: dict[str, str], drop: tuple[str, ...] = ()) -> None:
    values = read_env()
    values.update(updates)
    for key in drop:
        values.pop(key, None)
    path = env_file()
    path.write_text("".join(f"{k}={v}\n" for k, v in values.items()))
    path.chmod(0o600)


def install_elan() -> bool:
    _say("elan (the Lean toolchain manager) is not installed.")
    if not _confirm(f"Install it to {toolchain.elan_home()}? [Y/n]: "):
        _say("Skipped — install elan yourself, or enter the devenv shell, then re-run.")
        return False
    try:
        installer = subprocess.run(["curl", "-sSf", ELAN_INSTALLER], capture_output=True, text=True, timeout=120)
        if installer.returncode != 0:
            _say(f"Could not download the elan installer: {installer.stderr.strip()}")
            return False
        result = subprocess.run(
            ["sh", "-s", "--", "-y", "--default-toolchain", "none"],
            input=installer.stdout,
            text=True,
        )
        return result.returncode == 0
    except (OSError, subprocess.SubprocessError) as e:
        _say(f"elan installation failed: {e}")
        return False


def _lake(*args: str, timeout: int = 3600) -> bool:
    lake = toolchain.which("lake")
    if lake is None:
        return False
    result = subprocess.run([lake, *args], cwd=str(LEAN_PROJECT_DIR), env=toolchain.env(), timeout=timeout)
    return result.returncode == 0


def install_lean() -> bool:
    if toolchain.which("lake") is None and not install_elan():
        return False

    if mathlib_lib().is_dir():
        _say("Lean toolchain and Mathlib already present — skipping.")
        return True

    toolchain_file = LEAN_PROJECT_DIR / "lean-toolchain"
    version = toolchain_file.read_text().strip() if toolchain_file.is_file() else "the pinned version"
    _say(f"Installing Lean {version} and Mathlib.")
    _say("This downloads several GB of prebuilt oleans and takes a few minutes.")
    if not _confirm("Continue? [Y/n]: "):
        _say("Skipped — no proofs can run until this completes.")
        return False

    for description, args in (
        ("Resolving dependencies", ("update",)),
        ("Fetching prebuilt Mathlib oleans", ("exe", "cache", "get")),
        ("Precompiling the warmup module", ("build", "Warmup")),
    ):
        _say(f"  {description}...")
        if not _lake(*args):
            _say(f"  Failed: lake {' '.join(args)}")
            return False
    return True


def _pick(options: list[str], prompt: str) -> str:
    _say("")
    for index, option in enumerate(options, start=1):
        _say(f"  {index}) {option}")
    while True:
        choice = _ask(prompt)
        if choice.isdigit() and 1 <= int(choice) <= len(options):
            return options[int(choice) - 1]
        _say("Invalid choice, try again.")


def _claude_models(config_dir: str) -> list[str]:
    try:
        result = subprocess.run(
            ["claude", "-p", "List only the model IDs you support, one per line, no explanation."],
            capture_output=True,
            text=True,
            timeout=120,
            env={**os.environ, "CLAUDE_CONFIG_DIR": config_dir},
        )
    except (OSError, subprocess.SubprocessError):
        return []
    return sorted(line.strip() for line in result.stdout.splitlines() if line.strip().startswith("claude"))


def _choose_model(models: list[str]) -> str:
    if models:
        return _pick(models, "Pick a number: ")
    _say("Could not fetch the model list.")
    model = _ask("Enter model name manually: ")
    if not model:
        raise SystemExit("A model name is required.")
    return model


def configure_claude_cli() -> None:
    raw = _ask("Claude config directory [~/.claude]: ", "~/.claude")
    config_dir = Path(raw).expanduser()
    if not config_dir.is_dir():
        raise SystemExit(f"'{config_dir}' is not a directory.")

    _say("Fetching available models via the claude CLI...")
    model = _choose_model(_claude_models(str(config_dir)))

    write_env(
        {
            "LLM_BACKEND": "claude-cli",
            "CLAUDE_CONFIG_DIR": str(config_dir),
            "LLM_MODEL": model,
            "PROOF_CACHE_TTL_DAYS": "7",
        },
        drop=("LLM_BASE_URL", "LLM_API_KEY"),
    )
    _say("")
    _say(f"Saved to {env_file()}")
    _say("  LLM_BACKEND       = claude-cli")
    _say(f"  CLAUDE_CONFIG_DIR = {config_dir}")
    _say(f"  LLM_MODEL         = {model}")


def configure_openai() -> None:
    _say("")
    _say("Common base URLs:")
    for name, url in (
        ("OpenAI", "https://api.openai.com/v1"),
        ("Anthropic", "https://api.anthropic.com/v1"),
        ("Groq", "https://api.groq.com/openai/v1"),
        ("Ollama", "http://localhost:11434/v1"),
        ("LM Studio", "http://localhost:1234/v1"),
    ):
        _say(f"  {name:<10} {url}")
    _say("")

    base_url = _ask("LLM_BASE_URL: ")
    if not base_url:
        raise SystemExit("A base URL is required.")
    api_key = getpass.getpass("LLM_API_KEY (blank for local models): ").strip()

    os.environ["LLM_BASE_URL"] = base_url
    os.environ["LLM_API_KEY"] = api_key
    _say("Fetching available models...")

    from .llm_client import list_models

    model = _choose_model(list_models())

    write_env(
        {
            "LLM_BACKEND": "openai",
            "LLM_BASE_URL": base_url,
            "LLM_API_KEY": api_key,
            "LLM_MODEL": model,
            "PROOF_CACHE_TTL_DAYS": "7",
        },
        drop=("CLAUDE_CONFIG_DIR",),
    )
    _say("")
    _say(f"Saved to {env_file()}")
    _say(f"  LLM_BASE_URL = {base_url}")
    _say(f"  LLM_MODEL    = {model}")


def configure_backend() -> None:
    _say("")
    _say("Choose a backend:")
    _say("  1) Claude Code  (local claude CLI — uses your Pro plan, no API key needed)")
    _say("  2) OpenAI-compatible API  (OpenAI, Anthropic, Groq, Ollama, LM Studio, …)")
    choice = _ask("Pick 1 or 2: ")
    if choice == "1":
        configure_claude_cli()
    elif choice == "2":
        configure_openai()
    else:
        raise SystemExit("Invalid choice.")


def run(lean_only: bool = False, backend_only: bool = False) -> int:
    if not backend_only and not install_lean():
        return 1
    if not lean_only:
        configure_backend()

    if sandbox.available() is None:
        _say("")
        _say("bubblewrap is not installed — Lean proofs will run unsandboxed.")
        _say("  Arch: pacman -S bubblewrap    Debian: apt install bubblewrap")

    _say("")
    _say("Check the installation with:  formal status")
    return 0
