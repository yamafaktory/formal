import logging
import os
import sys

# ── ANSI colours (disabled if not a TTY or NO_COLOR is set) ──────────────────
_USE_COLOR = sys.stdout.isatty() and not os.getenv("NO_COLOR")

_C = (
    {
        "reset": "\033[0m",
        "bold": "\033[1m",
        "grey": "\033[90m",
        "cyan": "\033[36m",
        "yellow": "\033[33m",
        "green": "\033[32m",
        "red": "\033[31m",
        "magenta": "\033[35m",
        "blue": "\033[34m",
    }
    if _USE_COLOR
    else {k: "" for k in ["reset", "bold", "grey", "cyan", "yellow", "green", "red", "magenta", "blue"]}
)


class _PipelineFormatter(logging.Formatter):
    _PREFIX = {
        "PIPELINE": ("cyan", "PIPELINE"),
        "SCREEN": ("magenta", "SCREEN  "),
        "VERIFY": ("yellow", "VERIFY  "),
        "LEAN": ("grey", "LEAN    "),
        "OK": ("green", "OK      "),
        "FAIL": ("red", "FAIL    "),
    }

    def format(self, record: logging.LogRecord) -> str:
        tag = getattr(record, "tag", "PIPELINE")
        colour, label = self._PREFIX.get(tag, ("grey", tag.ljust(8)))
        c = _C[colour]
        r = _C["reset"]
        b = _C["bold"]
        msg = record.getMessage()
        return f"{b}{c}[{label}]{r} {msg}"


def get_logger(name: str) -> logging.Logger:
    logger = logging.getLogger(name)
    if not logger.handlers:
        handler = logging.StreamHandler(sys.stdout)
        handler.setFormatter(_PipelineFormatter())
        logger.addHandler(handler)
        logger.setLevel(logging.DEBUG)
        logger.propagate = False
    return logger


def log(logger: logging.Logger, tag: str, msg: str) -> None:
    logger.info(msg, extra={"tag": tag})
