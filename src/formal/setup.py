"""Installation of the Lean toolchain, driven by `formal setup`."""

import shutil
import subprocess
from pathlib import Path

from . import sandbox, toolchain
from .paths import FORMAL_HOME, LEAN_PROJECT_DIR

ELAN_INSTALLER = "https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"


# Every key formal understands. A key outside this set is reported by `formal status`.
KNOWN_ENV_KEYS = frozenset(
    {
        "ELAN_HOME",
        "FORMAL_HOME",
        "FORMAL_HOST",
        "FORMAL_PORT",
        "FORMAL_RESULTS_DIR",
        "FORMAL_SANDBOX",
        "LEAN_PROJECT_DIR",
        "LEAN_TIMEOUT",
        "NO_COLOR",
        "PROOF_CACHE_DIR",
        "PROOF_CACHE_TTL_DAYS",
        "SESSION_TTL_MINUTES",
        "XDG_DATA_HOME",
    }
)


def unknown_env_keys() -> list[str]:
    """Keys present in .env that nothing reads — a silent misconfiguration."""
    return sorted(key for key in read_env() if key not in KNOWN_ENV_KEYS)


def env_file() -> Path:
    return FORMAL_HOME / ".env"


def mathlib_lib() -> Path:
    return LEAN_PROJECT_DIR / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib"


TEMPLATE_FILES = ("lakefile.toml", "lean-toolchain", "lake-manifest.json", "Warmup.lean")


def template_dir() -> Path:
    return Path(__file__).resolve().parent / "_lean_project"


def materialize_lean_project() -> bool:
    """Copy the bundled Lean project into FORMAL_HOME when running outside a checkout."""
    if (LEAN_PROJECT_DIR / "lakefile.toml").is_file():
        return True

    source = template_dir()
    if not source.is_dir():
        _say(f"No Lean project at {LEAN_PROJECT_DIR} and no bundled copy at {source}.")
        return False

    _say(f"Creating the Lean project in {LEAN_PROJECT_DIR}...")
    (LEAN_PROJECT_DIR / "Verify").mkdir(parents=True, exist_ok=True)
    for name in TEMPLATE_FILES:
        candidate = source / name
        if candidate.is_file():
            shutil.copy2(candidate, LEAN_PROJECT_DIR / name)
    return (LEAN_PROJECT_DIR / "lakefile.toml").is_file()


def manifest() -> Path:
    return LEAN_PROJECT_DIR / "lake-manifest.json"


def lean_version() -> str | None:
    toolchain_file = LEAN_PROJECT_DIR / "lean-toolchain"
    return toolchain_file.read_text().strip() if toolchain_file.is_file() else None


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


LEAN_INSTALL_DOCS = "https://lean-lang.org/install/"


def install_elan() -> bool:
    _say("elan (the Lean toolchain manager) is not installed.")
    _say(f"If your package manager provides it, prefer that — see {LEAN_INSTALL_DOCS}")
    _say("Any elan already on your system is used as-is, however it was installed.")
    _say("")
    if not _confirm(f"Otherwise, run elan's official installer into {toolchain.elan_home()}? [Y/n]: "):
        _say("Skipped — install elan, then re-run.")
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


def ensure_elan() -> bool:
    if toolchain.which("lake") or toolchain.which("elan"):
        return True
    return install_elan()


def toolchain_installed(elan: str, version: str) -> bool:
    try:
        result = subprocess.run(
            [elan, "toolchain", "list"],
            capture_output=True,
            text=True,
            env=toolchain.env(),
            timeout=60,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    if result.returncode != 0:
        return False
    return any(line.split()[0] == version for line in result.stdout.splitlines() if line.strip())


def ensure_toolchain() -> bool:
    elan = toolchain.which("elan")
    if elan is None:
        return toolchain.which("lake") is not None

    version = lean_version()
    if version is None:
        _say(f"Missing {LEAN_PROJECT_DIR / 'lean-toolchain'} — cannot tell which Lean version to install.")
        return False

    if toolchain_installed(elan, version):
        return True

    _say(f"Installing Lean {version} via elan (a few hundred MB)...")
    result = subprocess.run([elan, "toolchain", "install", version], env=toolchain.env())
    if result.returncode != 0:
        return False
    return toolchain.which("lake") is not None


def install_lean() -> bool:
    if not materialize_lean_project():
        return False
    if not ensure_elan() or not ensure_toolchain():
        return False

    if mathlib_lib().is_dir():
        _say("Mathlib already built — skipping.")
        return True

    _say("Fetching Mathlib.")
    _say("This downloads several GB of prebuilt oleans and takes a few minutes.")
    if not _confirm("Continue? [Y/n]: "):
        _say("Skipped — no proofs can run until this completes.")
        return False

    steps = [
        ("Fetching prebuilt Mathlib oleans", ("exe", "cache", "get")),
        ("Precompiling the warmup module", ("build", "Warmup")),
    ]
    if manifest().is_file():
        _say("  Using the dependency revisions pinned in lake-manifest.json.")
    else:
        steps.insert(0, ("Resolving dependencies", ("update",)))

    for description, args in steps:
        _say(f"  {description}...")
        if not _lake(*args):
            _say(f"  Failed: lake {' '.join(args)}")
            return False
    return True


def run() -> int:
    if not install_lean():
        return 1

    if sandbox.available() is None:
        _say("")
        _say("bubblewrap is not installed — Lean proofs will run unsandboxed.")
        _say("  Arch: pacman -S bubblewrap    Debian: apt install bubblewrap")

    _say("")
    _say("Check the installation with:  formal status")
    return 0
