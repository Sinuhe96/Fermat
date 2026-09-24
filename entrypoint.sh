#!/bin/sh
# Runtime bootstrap: installs the pinned Lean toolchain ONCE into the
# elan-home named volume, then execs the container command.
# Idempotent - subsequent starts skip the install instantly.
# NOTE: must stay LF-only; the Dockerfile strips any CR defensively.
set -eu
: "${LEAN_TOOLCHAIN:=leanprover/lean4:v4.35.0-rc2}"
if ! elan toolchain list 2>/dev/null | grep -q "$LEAN_TOOLCHAIN"; then
  echo "Installing Lean toolchain $LEAN_TOOLCHAIN (one-time)..."
  elan toolchain install "$LEAN_TOOLCHAIN"
fi
elan default "$LEAN_TOOLCHAIN" >/dev/null 2>&1 || true
export PATH="$ELAN_HOME/bin:$PATH"
exec "$@"
