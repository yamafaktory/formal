#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
ENV_FILE="$ROOT/.env"
LEAN_DIR="$ROOT/lean_project"
ELAN_BIN="${ELAN_HOME:-$HOME/.elan}/bin"

cat <<'EOF'

Formal Verifier — Setup

EOF

_upsert() {
	local key="$1" val="$2" file="$3"
	if [[ -f "$file" ]] && grep -q "^${key}=" "$file"; then
		sed -i "s|^${key}=.*|${key}=${val}|" "$file"
	else
		echo "${key}=${val}" >>"$file"
	fi
}

_drop() {
	[[ -f "$2" ]] || return 0
	sed -i "/^$1=/d" "$2"
}

_have() {
	command -v "$1" >/dev/null 2>&1
}

# ── Step 1: Python environment ────────────────────────────────────────────────

if ! _have uv; then
	echo "uv is required but not installed."
	echo "  https://docs.astral.sh/uv/getting-started/installation/"
	exit 1
fi

echo "[1/3] Syncing the Python environment..."
uv sync --project "$ROOT" --quiet
echo "      Done."
echo ""

# ── Step 2: Lean toolchain and Mathlib ────────────────────────────────────────

[[ -d "$ELAN_BIN" ]] && PATH="$ELAN_BIN:$PATH"

if ! _have elan; then
	echo "[2/3] Lean is not installed."
	echo "      elan (the Lean toolchain manager) will be installed to ${ELAN_BIN%/bin}."
	echo -n "      Install it now? [Y/n]: "
	read -r REPLY
	if [[ "${REPLY:-Y}" =~ ^[Nn] ]]; then
		echo "      Skipped. Install elan yourself, then re-run this script."
		exit 1
	fi
	curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh |
		sh -s -- -y --default-toolchain none
	PATH="$ELAN_BIN:$PATH"
fi

MATHLIB_LIB="$LEAN_DIR/.lake/packages/mathlib/.lake/build/lib"

if [[ -d "$MATHLIB_LIB" ]]; then
	echo "[2/3] Lean toolchain and Mathlib already present — skipping."
else
	echo "[2/3] Installing Lean $(tr -d '\n' <"$LEAN_DIR/lean-toolchain") and Mathlib."
	echo "      This downloads several GB of prebuilt oleans and takes a few minutes."
	echo -n "      Continue? [Y/n]: "
	read -r REPLY
	if [[ "${REPLY:-Y}" =~ ^[Nn] ]]; then
		echo "      Skipped. Re-run this script when ready — no proofs can run until then."
	else
		echo "      Resolving dependencies..."
		(cd "$LEAN_DIR" && lake update)
		echo "      Fetching prebuilt Mathlib oleans..."
		(cd "$LEAN_DIR" && lake exe cache get)
		echo "      Precompiling the warmup module..."
		(cd "$LEAN_DIR" && lake build Warmup)
		echo "      Done."
	fi
fi
echo ""

# ── Step 3: LLM backend ───────────────────────────────────────────────────────

echo "[3/3] Choose a backend:"
echo "  1) Claude Code  (local claude CLI — uses your Pro plan, no API key needed)"
echo "  2) OpenAI-compatible API  (OpenAI, Anthropic, Groq, Ollama, LM Studio, …)"
echo ""
echo -n "Pick 1 or 2: "
read -r BACKEND_CHOICE

# ── Option 1: Claude Code CLI ─────────────────────────────────────────────────
if [[ "$BACKEND_CHOICE" == "1" ]]; then
	echo ""
	echo -n "Claude config directory (default: ~/.claude, e.g. ~/.claude-work for a work account): "
	read -r CLAUDE_CONFIG_INPUT
	CLAUDE_CONFIG_INPUT="${CLAUDE_CONFIG_INPUT:-~/.claude}"
	CLAUDE_CONFIG_DIR="${CLAUDE_CONFIG_INPUT/#\~/$HOME}"

	if [[ ! -d "$CLAUDE_CONFIG_DIR" ]]; then
		echo "Error: '$CLAUDE_CONFIG_DIR' is not a directory."
		exit 1
	fi

	echo ""
	echo "Fetching available models via claude CLI..."
	MODELS=$(CLAUDE_CONFIG_DIR="$CLAUDE_CONFIG_DIR" claude -p \
		"List only the model IDs you support, one per line, no explanation." \
		2>/dev/null | grep -E "^claude" | sort || true)

	LLM_MODEL=""
	if [[ -z "$MODELS" ]]; then
		echo "Could not fetch models."
		echo -n "Enter model name manually: "
		read -r LLM_MODEL
		[[ -z "$LLM_MODEL" ]] && {
			echo "Model name is required."
			exit 1
		}
	else
		echo ""
		echo "Available models:"
		i=1
		while IFS= read -r model; do
			echo "  $i) $model"
			((i++))
		done <<<"$MODELS"

		while [[ -z "$LLM_MODEL" ]]; do
			echo -n "Pick a number: "
			read -r CHOICE
			LLM_MODEL=$(sed -n "${CHOICE}p" <<<"$MODELS")
			[[ -z "$LLM_MODEL" ]] && echo "Invalid choice, try again."
		done
	fi

	_upsert "LLM_BACKEND" "claude-cli" "$ENV_FILE"
	_upsert "CLAUDE_CONFIG_DIR" "$CLAUDE_CONFIG_DIR" "$ENV_FILE"
	_upsert "LLM_MODEL" "$LLM_MODEL" "$ENV_FILE"
	_upsert "PROOF_CACHE_TTL_DAYS" "7" "$ENV_FILE"
	for key in LLM_BASE_URL LLM_API_KEY; do
		_drop "$key" "$ENV_FILE"
	done

	cat <<EOF

Saved to $ENV_FILE
  LLM_BACKEND       = claude-cli
  CLAUDE_CONFIG_DIR = $CLAUDE_CONFIG_DIR
  LLM_MODEL         = $LLM_MODEL
EOF

# ── Option 2: OpenAI-compatible API ──────────────────────────────────────────
elif [[ "$BACKEND_CHOICE" == "2" ]]; then
	echo ""
	echo "Common base URLs:"
	echo "  OpenAI:    https://api.openai.com/v1"
	echo "  Anthropic: https://api.anthropic.com/v1"
	echo "  Groq:      https://api.groq.com/openai/v1"
	echo "  Ollama:    http://localhost:11434/v1"
	echo "  LM Studio: http://localhost:1234/v1"
	echo ""
	echo -n "LLM_BASE_URL: "
	read -r LLM_BASE_URL
	[[ -z "$LLM_BASE_URL" ]] && {
		echo "Base URL is required."
		exit 1
	}

	echo ""
	echo -n "LLM_API_KEY (leave blank for local models): "
	read -rs LLM_API_KEY
	echo ""

	echo ""
	echo "Fetching available models..."
	MODELS=""
	if [[ -n "$LLM_API_KEY" ]]; then
		MODELS=$(curl -sf "$LLM_BASE_URL/models" -H "Authorization: Bearer $LLM_API_KEY" |
			grep -o '"id":"[^"]*"' | sed 's/"id":"//;s/"//' | sort 2>/dev/null || true)
	else
		MODELS=$(curl -sf "$LLM_BASE_URL/models" |
			grep -o '"id":"[^"]*"' | sed 's/"id":"//;s/"//' | sort 2>/dev/null || true)
	fi

	LLM_MODEL=""
	if [[ -z "$MODELS" ]]; then
		echo "Could not fetch models (provider may not support GET /v1/models)."
		echo -n "Enter model name manually: "
		read -r LLM_MODEL
		[[ -z "$LLM_MODEL" ]] && {
			echo "Model name is required."
			exit 1
		}
	else
		echo ""
		echo "Available models:"
		i=1
		while IFS= read -r model; do
			echo "  $i) $model"
			((i++))
		done <<<"$MODELS"

		while [[ -z "$LLM_MODEL" ]]; do
			echo -n "Pick a number: "
			read -r CHOICE
			LLM_MODEL=$(sed -n "${CHOICE}p" <<<"$MODELS")
			[[ -z "$LLM_MODEL" ]] && echo "Invalid choice, try again."
		done
	fi

	_upsert "LLM_BACKEND" "openai" "$ENV_FILE"
	_upsert "LLM_BASE_URL" "$LLM_BASE_URL" "$ENV_FILE"
	_upsert "LLM_API_KEY" "$LLM_API_KEY" "$ENV_FILE"
	_upsert "LLM_MODEL" "$LLM_MODEL" "$ENV_FILE"
	_upsert "PROOF_CACHE_TTL_DAYS" "7" "$ENV_FILE"
	_drop "CLAUDE_CONFIG_DIR" "$ENV_FILE"

	cat <<EOF

Saved to $ENV_FILE
  LLM_BASE_URL = $LLM_BASE_URL
  LLM_MODEL    = $LLM_MODEL
EOF

else
	echo "Invalid choice."
	exit 1
fi

for key in COMPOSE_FILE HOST_CLAUDE_CONFIG_DIR CLAUDE_CLI_CMD; do
	_drop "$key" "$ENV_FILE"
done

chmod 600 "$ENV_FILE"

echo ""
if ! _have lake; then
	echo "Add Lean to your PATH, then open a new shell:"
	echo "  fish:  fish_add_path $ELAN_BIN"
	echo "  bash:  export PATH=\"$ELAN_BIN:\$PATH\""
	echo ""
fi
cat <<EOF
Check the installation:
  $ROOT/formal status

Verify a file:
  $ROOT/formal verify path/to/File.java
EOF
