# ── Stage 1: Install Lean + cache Mathlib oleans ─────────────────────────────
FROM debian:bookworm-slim AS lean-builder

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        apt-utils curl ca-certificates git \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:$PATH"

# Set up Lean project — elan reads lean-toolchain and installs the right version
WORKDIR /lean_project
COPY lean_project/lean-toolchain lean_project/lakefile.toml ./

# Install the pinned Lean version and download prebuilt Mathlib oleans
RUN echo "[1/3] Resolving Lean toolchain and Mathlib dependencies..." \
    && lake update \
    && echo "[2/3] Fetching prebuilt Mathlib oleans from cache..."
RUN lake exe cache get \
    && echo "[2/3] Oleans ready."

# Precompile common Mathlib imports — bakes oleans into the image so the first
# real proof request hits the cache instead of recompiling from scratch
COPY lean_project/Warmup.lean ./
RUN echo "[3/3] Precompiling Mathlib warmup module (this takes a few minutes)..." \
    && lake build Warmup \
    && echo "[3/3] Warmup complete. Lean stage done."

# ── Stage 2: Final image ──────────────────────────────────────────────────────
FROM debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        apt-utils curl ca-certificates git \
        python3 python3-pip python3-venv \
    && rm -rf /var/lib/apt/lists/*

# Copy elan + installed Lean toolchain from builder
COPY --from=lean-builder /root/.elan /root/.elan
ENV PATH="/root/.elan/bin:$PATH"

# Copy the fully-resolved Lean project (lake packages + cached oleans)
COPY --from=lean-builder /lean_project /lean_project
COPY lean_project/Verify/.gitkeep /lean_project/Verify/.gitkeep

# Install the application and its dependencies
WORKDIR /app
RUN python3 -m venv /venv
ENV PATH="/venv/bin:$PATH"
COPY pyproject.toml README.md ./
COPY src ./src
RUN pip install --no-cache-dir .

ENV LEAN_PROJECT_DIR=/lean_project
ENV LEAN_TIMEOUT=120
ENV MAX_PROOF_RETRIES=3
ENV MAX_PARALLEL_PROPERTIES=4

EXPOSE 1337
CMD ["uvicorn", "formal.api:app", "--host", "0.0.0.0", "--port", "1337"]
