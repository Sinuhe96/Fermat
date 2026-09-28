"""Sympy screen for chunk B-01 - section B (p. 2 R1) of PROOF_of_FERMAT.pdf.

The two rules the main proof cites as "muc B.1 / B.2, trang 2":

  B.1  sum_{i=k}^{n} a_i = sum_{i=m}^{n+m-k} a_{i-m+k},  k, m in N
  B.2  sum_{i=k}^{m-1} i(i-1)...(i-k+1) h^(m-1-i) x^(i-k)
         = sum_{i=0}^{m-1-k} (m-1-i)(m-2-i)...(m-k-i) h^i x^(m-1-k-i)
         = f^(k)(x),   f(x) = (x^m - h^m)/(x - h)

Both are identities rather than congruences and hold for every admissible
parameter, so - unlike the FLT-equation lemmas L1/L2/L6 - this screen runs on
real instances: random sequences for B.1, and exact symbolic differentiation
for B.2. The checks live in 04-sympy/m1_common.py (`screen_section_B`), which
the whole M1 lane shares; this file is the chunk-level entry point so
`run_all.py` covers the chunk.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

import m1_common


def main() -> int:
    ok = m1_common.screen_section_B()
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
