FROM ubuntu:24.04

# The image contains tools only; credentials are mounted at runtime. That
# runtime has a read-only root and no sudo, with elan mounted read-only.
RUN apt-get update && apt-get install --yes --no-install-recommends \
    bash build-essential ca-certificates curl file git libgmp-dev \
    nodejs npm patch python3 ripgrep unzip \
    && rm -rf /var/lib/apt/lists/*
RUN npm install --global @openai/codex@0.166.0
USER nobody
