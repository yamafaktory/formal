"""Command-line entry point — installs the toolchain and runs the server."""

import argparse
import os
import sys


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


def _cmd_status(args: argparse.Namespace) -> int:
    from . import sandbox, server, setup, toolchain
    from .paths import FORMAL_HOME, LEAN_PROJECT_DIR, PROOF_CACHE_DIR

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
        ("server", f"{server.base_url()} ({'running' if server.is_running() else 'not running'})"),
    ]

    unknown = setup.unknown_env_keys()
    if unknown:
        rows.append(("unused .env keys", f"{', '.join(unknown)} — nothing reads these"))

    width = max(len(k) for k, _ in rows)
    for key, value in rows:
        print(f"{key.ljust(width)}  {value}")

    return 0 if lean_ok else 1


def _cmd_serve(args: argparse.Namespace) -> int:
    from . import server

    if server.is_running(args.host, args.port):
        print(f"already serving on {server.base_url(args.host, args.port)}")
        return 0

    if args.background:
        url = server.start(args.host, args.port)
        print(f"serving on {url} (log: {server.log_file()})")
        return 0

    import uvicorn

    uvicorn.run("formal.api:app", host=args.host, port=args.port, log_level="info")
    return 0


def _cmd_stop(args: argparse.Namespace) -> int:
    from . import server

    if server.stop(args.host, args.port):
        print("stopped")
        return 0
    if server.is_running(args.host, args.port):
        print(
            f"something is serving on {server.base_url(args.host, args.port)} but formal did not start it",
            file=sys.stderr,
        )
        return 1
    print("not running")
    return 0


def _cmd_setup(args: argparse.Namespace) -> int:
    from . import setup

    return setup.run()


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="formal",
        description="Property checker for code, backed by Lean 4. Agents drive it over HTTP.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    status = sub.add_parser("status", help="show the resolved configuration and toolchain state")
    status.set_defaults(func=_cmd_status)

    from . import server

    serve = sub.add_parser("serve", help="run the HTTP API")
    serve.add_argument("--host", default=server.host())
    serve.add_argument("--port", type=int, default=server.port())
    serve.add_argument(
        "--background",
        action="store_true",
        help="start detached and return once the server answers",
    )
    serve.set_defaults(func=_cmd_serve)

    stop = sub.add_parser("stop", help="stop a server started with --background")
    stop.add_argument("--host", default=server.host())
    stop.add_argument("--port", type=int, default=server.port())
    stop.set_defaults(func=_cmd_stop)

    setup = sub.add_parser("setup", help="install the Lean toolchain and Mathlib")
    setup.set_defaults(func=_cmd_setup)

    return parser


def main() -> int:
    _load_env()
    parser = _build_parser()
    args = parser.parse_args()

    try:
        return args.func(args)
    except KeyboardInterrupt:
        return 130
    except RuntimeError as e:
        print(f"formal: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
