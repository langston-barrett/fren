FROM ubuntu:24.04@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852

# Tools only. PR code runs later, as an unprivileged user in a private
# container; neither Docker build nor this image receives credentials.
RUN apt-get update && apt-get install --yes --no-install-recommends \
    bash build-essential ca-certificates cmake curl elan file git gnupg \
    libgmp-dev ninja-build pkg-config procps python3 unzip util-linux xz-utils zstd \
    && rm -rf /var/lib/apt/lists/*
ARG LLVM_VERSION=none
# Coverage's runtime and llvm-cov must match the PR toolchain's clang.
# worker.py obtains this number in isolation, and accepts digits only.
RUN if [ "$LLVM_VERSION" != none ]; then \
      curl -fsSL https://apt.llvm.org/llvm-snapshot.gpg.key -o /tmp/llvm.asc && \
      test "$(gpg --show-keys --with-colons /tmp/llvm.asc \
        | awk -F: '$1 == "pub" { primary = 1 } $1 == "fpr" && primary { print $10; primary = 0 }')" \
        = 6084F3CF814B57C1CF12EFD515CF4D18AF4F7421 && \
      gpg --dearmor -o /usr/share/keyrings/llvm.gpg /tmp/llvm.asc && \
      printf 'deb [signed-by=/usr/share/keyrings/llvm.gpg] http://apt.llvm.org/noble/ llvm-toolchain-noble-%s main\n' "$LLVM_VERSION" \
        > /etc/apt/sources.list.d/llvm.list && \
      apt-get update && apt-get install --yes --no-install-recommends \
        "libclang-rt-$LLVM_VERSION-dev" "llvm-$LLVM_VERSION" gdb && \
      gdb -q -nx -batch -ex 'python import gdb' && \
      rm -rf /var/lib/apt/lists/* /tmp/llvm.asc; \
    fi
USER nobody
