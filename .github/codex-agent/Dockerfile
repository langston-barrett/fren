FROM ubuntu:24.04@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852

# The image contains tools only; credentials are mounted at runtime. That
# runtime has a read-only root and no sudo, with elan mounted read-only.
RUN apt-get update && apt-get install --yes --no-install-recommends \
    bash build-essential ca-certificates curl file git libgmp-dev \
    nodejs npm patch python3 ripgrep unzip \
    && rm -rf /var/lib/apt/lists/*
# The lock includes the CLI and every optional platform package, with
# registry integrity hashes. npm ci rejects drift instead of resolving it.
COPY package.json package-lock.json /opt/codex/
RUN npm ci --prefix /opt/codex --ignore-scripts --no-audit --no-fund \
    && ln -s /opt/codex/node_modules/.bin/codex /usr/local/bin/codex
# Optional-package failures must not leave an image with no usable binary.
RUN --network=none codex --version
USER nobody
