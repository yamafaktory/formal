# ── Stage 1: Install Lean + cache Mathlib oleans ─────────────────────────────
FROM debian:bookworm-slim AS lean-builder

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates git \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:$PATH"

# Set up Lean project — elan reads lean-toolchain and installs the right version
WORKDIR /lean_project
COPY lean_project/lean-toolchain lean_project/lakefile.toml ./

# Install the pinned Lean version and download prebuilt Mathlib oleans
RUN lake update && lake exe cache get

# ── Stage 2: Final image ──────────────────────────────────────────────────────
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates git \
        python3 python3-pip \
    && rm -rf /var/lib/apt/lists/*

# Copy elan + installed Lean toolchain from builder
COPY --from=lean-builder /root/.elan /root/.elan
ENV PATH="/root/.elan/bin:$PATH"

# Copy the fully-resolved Lean project (lake packages + cached oleans)
COPY --from=lean-builder /lean_project /lean_project
COPY lean_project/Verify/.gitkeep /lean_project/Verify/.gitkeep

# Install Python dependencies
WORKDIR /app
COPY requirements.txt .
RUN pip3 install --break-system-packages --no-cache-dir -r requirements.txt

# Copy the application (build context IS the formal/ package)
COPY *.py ./formal/

ENV LEAN_PROJECT_DIR=/lean_project
ENV LEAN_TIMEOUT=120
ENV MAX_PROOF_RETRIES=3
ENV MAX_PARALLEL_PROPERTIES=4
ENV PYTHONPATH=/app

EXPOSE 1337
CMD ["uvicorn", "formal.api:app", "--host", "0.0.0.0", "--port", "1337"]
