#!/bin/sh
# Environment check for the fermat-lean container.
# Run:  docker compose exec lean sh /workspace/proof/check_env.sh
set -u
echo "--- Lean toolchain ---"
lean --version || echo "MISSING lean"
lake --version || echo "MISSING lake"
echo "--- Python / sympy (brute-force lemma checks) ---"
python3 -c "import sympy; print('sympy', sympy.__version__)" || echo "MISSING sympy"
echo "--- misc ---"
git --version || echo "MISSING git"
echo "--- toolchain volume ---"
du -sh "${ELAN_HOME:-/elan-home}" 2>/dev/null || true
