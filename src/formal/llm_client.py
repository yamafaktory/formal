"""
LLM client — two backends:

  LLM_BACKEND=claude-cli   Shell out to the local `claude` CLI (Claude Code / Pro plan).
                            No API key needed. Requires claude to be installed on the host
                            and mounted into the container.

  LLM_BACKEND=openai       Use any OpenAI-compatible HTTP API.
                            Requires LLM_BASE_URL, LLM_API_KEY, LLM_MODEL.
                            Works with OpenAI, Anthropic, Groq, Ollama, LM Studio, etc.
"""

import os
import re
import subprocess

# ── Helpers ───────────────────────────────────────────────────────────────────


def extract_code_block(text: str, lang: str = "") -> str:
    """Extract the content of the first fenced code block matching lang."""
    pattern = rf"```{re.escape(lang)}\n(.*?)```" if lang else r"```\w*\n(.*?)```"
    match = re.search(pattern, text, re.DOTALL)
    return match.group(1).strip() if match else ""


# ── Claude CLI backend ────────────────────────────────────────────────────────


def _call_cli(system: str, user: str, model: str | None = None) -> str:
    prompt = f"{system}\n\n{user}"
    cli_cmd = os.getenv("LLM_CLI_CMD", "claude")
    cmd = [cli_cmd, "-p", prompt]
    if model:
        cmd += ["--model", model]

    timeout = int(os.getenv("LLM_TIMEOUT", "480"))
    last_error = ""
    for attempt in range(2):
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            # Observed as an outright stall rather than slow progress, and unrelated to
            # input size — so a second attempt usually succeeds where waiting would not.
            if attempt == 0:
                continue
            raise RuntimeError(
                f"{cli_cmd} stalled twice without responding, {timeout}s each time. "
                "Concurrent invocations make this more likely: lower MAX_PARALLEL_PROPERTIES, "
                "or raise LLM_TIMEOUT if your backend is genuinely just slow."
            ) from None
        if result.returncode == 0:
            return result.stdout.strip()
        # Prefer stderr; fall back to stdout; fall back to exit code
        last_error = result.stderr.strip() or result.stdout.strip() or f"exit code {result.returncode}"
        if attempt == 0:
            continue  # one retry for transient failures
    raise RuntimeError(f"LLM CLI error: {last_error}")


# ── OpenAI-compatible backend ─────────────────────────────────────────────────

_openai_client = None


def _get_openai_client():
    global _openai_client
    if _openai_client is None:
        from openai import OpenAI

        base_url = os.environ.get("LLM_BASE_URL", "").strip()
        api_key = os.environ.get("LLM_API_KEY", "").strip() or "no-key"
        if not base_url:
            raise RuntimeError("LLM_BASE_URL is not set. Run `formal setup` to configure your LLM provider.")
        _openai_client = OpenAI(base_url=base_url, api_key=api_key)
    return _openai_client


def _call_openai(system: str, user: str, model: str | None = None) -> str:
    model = model or os.environ.get("LLM_MODEL", "").strip()
    if not model:
        raise RuntimeError("LLM_MODEL is not set. Run `formal setup` to choose a model.")

    kwargs = {}
    # Sampling makes decomposition vary between runs on identical input. Blank
    # omits the parameter entirely, for models that reject it.
    temperature = os.environ.get("LLM_TEMPERATURE", "0").strip()
    if temperature:
        kwargs["temperature"] = float(temperature)

    response = _get_openai_client().chat.completions.create(
        model=model,
        messages=[
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
        max_tokens=4096,
        **kwargs,
    )
    return response.choices[0].message.content or ""


def list_models() -> list[str]:
    """Fetch available models (OpenAI backend only)."""
    try:
        models = _get_openai_client().models.list()
        return sorted(m.id for m in models.data)
    except Exception:
        return []


# ── Public interface ──────────────────────────────────────────────────────────


def call_llm(system: str, user: str, model: str | None = None) -> str:
    backend = os.environ.get("LLM_BACKEND", "openai").strip().lower()
    if backend == "claude-cli":
        return _call_cli(system, user, model)
    return _call_openai(system, user, model)
