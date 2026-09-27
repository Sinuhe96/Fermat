"""Smoke test for chunk L7-FRAG-05 (bổ đề 7: n ≡ 1 (mod 6)).

Real-instance screen (see l7_common) plus the printed reductio's algebraic
step: at every prime n ≡ 5 (mod 6) the number (n−2)/3 = 2l−1 is odd and, on
instances of (19)/(20), the printed sum collapses to 3a^{n(n−2)} (mod n²) —
which is what makes the printed absurdity work.
"""
import sys

from l7_common import CLAIMS, PRIMES, reductio_screen, run

WANT = ["n = 1 (mod 6)"]

if __name__ == "__main__":
    sys.exit(run({k: CLAIMS[k] for k in WANT}, PRIMES,
                 extra=[("S16 substitution (n ≡ 5 mod 6)", reductio_screen)]))
