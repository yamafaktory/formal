"""Command-line entry point — runs the verification pipeline in-process."""

import argparse
import json
import os
import shutil
import sys
from pathlib import Path


def _load_env() -> None:
    from .home import home

    candidate = home() / ".env"
    if not candidate.is_file():
        return
    for raw in candidate.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, value = line.partition("=")
        os.environ.setdefault(key.strip(), value.strip().strip("'\""))


def _result_to_dict(result) -> dict:
    return {
        "feature_file": result.feature_file,
        "feature_summary": result.feature_summary,
        "pure_functions": result.pure_functions,
        "impure_parts": result.impure_parts,
        "properties_found": result.properties_found,
        "properties_verified": result.properties_verified,
        "properties_unverifiable": result.properties_unverifiable,
        "properties_errored": result.properties_errored,
        "overall_score": result.overall_score,
        "results": [r.__dict__ for r in result.results],
    }


def _cmd_verify(args: argparse.Namespace) -> int:
    from .feature_pipeline import run_feature_pipeline, run_feature_pipeline_from_file

    if args.code:
        result = run_feature_pipeline(
            args.code,
            feature_file="<inline>",
            parallel=not args.no_parallel,
            language=args.lang or "Python",
        )
    else:
        path = Path(args.file).expanduser()
        if not path.is_file():
            print(f"formal: no such file: {path}", file=sys.stderr)
            return 2
        result = run_feature_pipeline_from_file(str(path), language=args.lang)

    if args.json:
        print(json.dumps(_result_to_dict(result), indent=2))
    else:
        print(result.summary())

    if result.properties_errored:
        return 2
    if result.overall_score == "no_pure_logic":
        return 3
    return 0 if result.overall_score == "full" else 1


def _cmd_status(args: argparse.Namespace) -> int:
    from . import sandbox, setup, toolchain
    from .paths import FORMAL_HOME, LEAN_PROJECT_DIR, PROOF_CACHE_DIR

    backend = os.getenv("LLM_BACKEND", "openai").strip().lower()
    model = os.getenv("LLM_MODEL", "").strip()

    if backend == "claude-cli":
        cli_cmd = os.getenv("LLM_CLI_CMD", "claude")
        llm_ok = shutil.which(cli_cmd) is not None
        llm_detail = f"{cli_cmd} ({'found' if llm_ok else 'not on PATH'})"
    else:
        base_url = os.getenv("LLM_BASE_URL", "").strip()
        llm_ok = bool(base_url)
        llm_detail = base_url or "LLM_BASE_URL not set"

    lake = toolchain.which("lake")
    toolchain_file = LEAN_PROJECT_DIR / "lean-toolchain"
    mathlib_oleans = LEAN_PROJECT_DIR / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib"
    lean_ok = lake is not None and mathlib_oleans.is_dir()

    rows = [
        ("home", str(FORMAL_HOME)),
        ("lean project", str(LEAN_PROJECT_DIR)),
        ("proof cache", str(PROOF_CACHE_DIR)),
        ("lake", lake or "not on PATH"),
        ("lean toolchain", toolchain_file.read_text().strip() if toolchain_file.is_file() else "missing"),
        ("mathlib oleans", "built" if mathlib_oleans.is_dir() else "missing — run: formal setup"),
        ("lean sandbox", sandbox.describe()),
        ("llm backend", backend),
        ("llm endpoint", llm_detail),
        ("llm model", model or "not set"),
    ]

    unknown = setup.unknown_env_keys()
    if unknown:
        rows.append(("unused .env keys", f"{', '.join(unknown)} — nothing reads these"))

    width = max(len(k) for k, _ in rows)
    for key, value in rows:
        print(f"{key.ljust(width)}  {value}")

    return 0 if lean_ok and llm_ok and model else 1


def _cmd_serve(args: argparse.Namespace) -> int:
    import uvicorn

    uvicorn.run("formal.api:app", host=args.host, port=args.port, log_level="info")
    return 0


def _cmd_setup(args: argparse.Namespace) -> int:
    from . import setup

    return setup.run(lean_only=args.lean_only, backend_only=args.backend_only)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="formal",
        description="LLM-driven property checker for code, backed by Lean 4.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    verify = sub.add_parser("verify", help="verify a source file or a snippet")
    verify.add_argument("file", nargs="?", help="path to the source file")
    verify.add_argument("--code", help="verify inline code instead of a file")
    verify.add_argument("--lang", help="source language (auto-detected from the extension)")
    verify.add_argument("--no-parallel", action="store_true", help="verify properties one at a time")
    verify.add_argument("--json", action="store_true", help="emit the full result as JSON")
    verify.set_defaults(func=_cmd_verify)

    status = sub.add_parser("status", help="show the resolved configuration and toolchain state")
    status.set_defaults(func=_cmd_status)

    serve = sub.add_parser("serve", help="run the HTTP API")
    serve.add_argument("--host", default="127.0.0.1")
    serve.add_argument("--port", type=int, default=1337)
    serve.set_defaults(func=_cmd_serve)

    setup = sub.add_parser("setup", help="install the Lean toolchain and configure the LLM backend")
    setup.add_argument("--lean-only", action="store_true", help="install Lean and Mathlib, skip backend configuration")
    setup.add_argument("--backend-only", action="store_true", help="configure the LLM backend, skip the Lean install")
    setup.set_defaults(func=_cmd_setup)

    return parser


def main() -> int:
    _load_env()
    parser = _build_parser()
    args = parser.parse_args()

    if args.command == "verify" and not args.file and not args.code:
        parser.error("verify needs a file path or --code")
    if args.command == "verify" and args.file and args.code:
        parser.error("verify takes a file path or --code, not both")

    try:
        return args.func(args)
    except KeyboardInterrupt:
        return 130
    except RuntimeError as e:
        print(f"formal: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
