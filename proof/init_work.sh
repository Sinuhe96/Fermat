#!/bin/sh
# init_work.sh — one-time initialization of the Linux Lake workspace.
#
# Run ONCE on a fresh machine, inside the container:
#   docker compose exec -T lean sh /workspace/proof/init_work.sh
#
# What it does (idempotent — every step skips when already done):
#   1. checks the pinned Lean toolchain is installed (entrypoint does this
#      at container start; this only verifies);
#   2. creates /workspace/work/testproj (`lake new testproj math`) and pins
#      lean-toolchain to LEAN_TOOLCHAIN;
#   3. fetches Mathlib at the pinned rev (`lake update`), downloads the
#      prebuilt oleans (`lake exe cache get`, ~450 MB into the lake-cache
#      volume) and unpacks them (`lake exe cache unpack`);
#   4. verifies Mathlib.olean exists and runs the fast readiness check.
#
# First run needs network and takes a while (toolchain ~500 MB is already
# handled at container start; Mathlib source + oleans total ~8 GB in the
# lake-work volume). Re-runs finish in seconds.
#
# The repo's chunk wiring (pipeline/03-lean/lakefile.toml) is NOT synced
# here — proof/compile_lean.sh syncs it on every compile.
#
# Must stay LF-only (see Dockerfile layer 3 note on CRLF shebangs).
set -eu

WORK=/workspace/work
PROJ=$WORK/testproj
TOOLCHAIN=leanprover/lean4:v4.35.0-rc2
MATHLIB_REV=v4.35.0-rc2
OLEAN=$PROJ/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean

case "${1-}" in
  "") set -- ;;
  *)
    echo "usage: $0" >&2
    exit 2
    ;;
esac

if [ ! -d "$WORK" ]; then
  echo "init_work.sh must run inside the lean container:" >&2
  echo "  docker compose exec -T lean sh /workspace/proof/init_work.sh" >&2
  exit 1
fi

echo "==> 1/4 toolchain (expect $TOOLCHAIN)"
if ! lean --version 2>/dev/null | grep -q "4.35.0-rc2"; then
  echo "FAIL: Lean 4.35.0-rc2 not installed." >&2
  echo "Restart the container so the entrypoint installs it:" >&2
  echo "  docker compose restart lean" >&2
  exit 1
fi
echo "toolchain: OK ($(lean --version))"

echo "==> 2/4 Lake project skeleton ($PROJ)"
if [ -f "$PROJ/lakefile.toml" ] && [ -f "$PROJ/lean-toolchain" ]; then
  echo "project: already present, skip 'lake new'"
else
  cd "$WORK"
  lake new testproj math
  echo "project: created"
fi
printf '%s\n' "$TOOLCHAIN" > "$PROJ/lean-toolchain"
echo "toolchain pin: OK"

echo "==> 3/4 Mathlib dependency + prebuilt oleans (rev $MATHLIB_REV)"
if [ -f "$OLEAN" ]; then
  echo "mathlib: Mathlib.olean present, skip update/get/unpack"
else
  cd "$PROJ"
  echo "--- lake update (fetches Mathlib source; needs network) ---"
  lake update
  echo "--- lake exe cache get (~450 MB download) ---"
  lake exe cache get
  echo "--- lake exe cache unpack ---"
  lake exe cache unpack
fi

echo "==> 4/4 verify"
if [ ! -f "$OLEAN" ]; then
  echo "FAIL: $OLEAN still missing after get/unpack." >&2
  echo "Check network access and re-run this script." >&2
  exit 1
fi
echo "mathlib: OK ($OLEAN)"
sh /workspace/proof/check_env.sh
echo "init_work.sh: DONE"
