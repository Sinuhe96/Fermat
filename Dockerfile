# fermat-lean: Lean 4 + Mathlib-ready dev image (Debian bookworm slim)
#
# Layering strategy (IMPORTANT): order layers from most-stable to
# least-stable so a rebuild after a late failure reuses cached early
# layers instead of restarting from scratch:
#   1. OS packages (changes rarely)          -> cached for months
#   2. elan bootstrap only (tiny, no toolchain -> cached; ~100MB download runs
#      ONCE at container first-start into the lean-elan volume, not here)
#   3. Config + entrypoint (changes sometimes -> rebuilds in seconds)
ARG DEBIAN_TAG=bookworm-slim
FROM debian:${DEBIAN_TAG}

ENV DEBIAN_FRONTEND=noninteractive

# --- Layer 1 (stable): OS packages + python/sympy -----------------------
RUN apt-get update && apt-get install -y --no-install-recommends \
      curl git ca-certificates zstd \
      python3 python3-pip python3-sympy \
    && rm -rf /var/lib/apt/lists/*

# --- Layer 2 (stable): elan bootstrap, NO toolchain ----------------------
# The ~500MB Lean toolchain is NOT baked in. entrypoint.sh installs it
# once into the lean-elan named volume on first `compose up`.
# ELAN_HOME + PATH are image ENV (not just exported at runtime) so that
# `docker compose exec` shells — which do not inherit the entrypoint's
# environment — still resolve lean/lake.
ENV ELAN_HOME=/elan-home \
    PATH=/elan-home/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
    LEAN_TOOLCHAIN=leanprover/lean4:v4.35.0-rc2
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf \
      | sh -s -- -y --no-modify-path --default-toolchain none \
    && ln -sf "$ELAN_HOME/bin/elan" /usr/local/bin/elan \
    && elan --version

# --- Layer 3 (volatile): runtime config only -----------------------------
# Windows hosts can hand us CRLF script files; a CR in the shebang makes
# /bin/sh\r unresolvable and the container dies with "no such file or
# directory". Strip CR defensively so a checkout on any OS builds cleanly.
COPY entrypoint.sh /usr/local/bin/fermat-entrypoint.sh
RUN sed -i 's/\r$//' /usr/local/bin/fermat-entrypoint.sh \
    && chmod +x /usr/local/bin/fermat-entrypoint.sh \
    && test "$(head -c 10 /usr/local/bin/fermat-entrypoint.sh | head -1)" = "#!/bin/sh" \
    && printf '#!/bin/sh\nexport ELAN_HOME="${ELAN_HOME:-/elan-home}"\nexport PATH="$ELAN_HOME/bin:$PATH"\n' \
         > /etc/profile.d/elan.sh \
    && python3 -c "import sympy; print('sympy', sympy.__version__)"

WORKDIR /workspace
ENTRYPOINT ["/usr/local/bin/fermat-entrypoint.sh"]
CMD ["bash", "-l"]
