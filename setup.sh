#!/usr/bin/env bash
set -euo pipefail

ENV_FILE="$(dirname "$0")/.env"

cat <<'EOF'

Formal Verifier — Setup

EOF

echo "Choose a backend:"
echo "  1) Claude Code  (local claude CLI — uses your Pro plan, no API key needed)"
echo "  2) OpenAI-compatible API  (OpenAI, Anthropic, Groq, Ollama, LM Studio, …)"
echo ""
echo -n "Pick 1 or 2: "
read -r BACKEND_CHOICE

_upsert() {
	local key="$1" val="$2" file="$3"
	if [[ -f "$file" ]] && grep -q "^${key}=" "$file"; then
		sed -i "s|^${key}=.*|${key}=${val}|" "$file"
	else
		echo "${key}=${val}" >>"$file"
	fi
}

# ── Option 1: Claude Code CLI ─────────────────────────────────────────────────
if [[ "$BACKEND_CHOICE" == "1" ]]; then
	echo ""
	echo -n "Claude config directory (default: ~/.claude, e.g. ~/.claude-work for a work account): "
	read -r CLAUDE_CONFIG_INPUT
	CLAUDE_CONFIG_INPUT="${CLAUDE_CONFIG_INPUT:-~/.claude}"
	# Expand ~ manually since it won't expand inside quotes later
	HOST_CLAUDE_CONFIG_DIR="${CLAUDE_CONFIG_INPUT/#\~/$HOME}"

	if [[ ! -d "$HOST_CLAUDE_CONFIG_DIR" ]]; then
		echo "Error: '$HOST_CLAUDE_CONFIG_DIR' is not a directory."
		exit 1
	fi

	echo ""
	echo "Fetching available models via claude CLI..."
	MODELS=$(CLAUDE_CONFIG_DIR="$HOST_CLAUDE_CONFIG_DIR" claude -p \
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
	_upsert "HOST_CLAUDE_CONFIG_DIR" "$HOST_CLAUDE_CONFIG_DIR" "$ENV_FILE"
	_upsert "LLM_MODEL" "$LLM_MODEL" "$ENV_FILE"
	_upsert "PROOF_CACHE_TTL_DAYS" "7" "$ENV_FILE"
	_upsert "COMPOSE_FILE" "docker-compose.yml:docker-compose.claude.yml" "$ENV_FILE"
	# Remove OpenAI-specific keys if switching backends
	sed -i '/^LLM_BASE_URL=/d; /^LLM_API_KEY=/d; /^LLM_CLI_CMD=/d' "$ENV_FILE" 2>/dev/null || true

	cat <<EOF

Saved to $ENV_FILE
  LLM_BACKEND           = claude-cli
  HOST_CLAUDE_CONFIG_DIR = $HOST_CLAUDE_CONFIG_DIR
  LLM_MODEL             = $LLM_MODEL

Run:  docker compose up          # pulls prebuilt image from GHCR
      docker compose up --build  # or build locally from source
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
	_upsert "COMPOSE_FILE" "docker-compose.yml" "$ENV_FILE"

	cat <<EOF

Saved to $ENV_FILE
  LLM_BASE_URL = $LLM_BASE_URL
  LLM_MODEL    = $LLM_MODEL

Run:  docker compose up          # pulls prebuilt image from GHCR
      docker compose up --build  # or build locally from source
EOF

else
	echo "Invalid choice."
	exit 1
fi

chmod 600 "$ENV_FILE"
