"""Smoke test for chunk L7-FRAG-03 (bổ đề 7: the b^{3n}+c^{3n} chain, (19), (20)).

Real-instance screen: see l7_common. Exit 0 = no counterexample.
"""
import sys

from l7_common import CLAIMS, PRIMES, run

WANT = ["S5 b^{2n}+a^n c^n = 0 mod n",
        "S6 b^{3n}+c^{3n} = 0 mod n",
        "(19/5.9) b^{3n}+c^{3n} = 0",
        "(5.10) a^{3n}+c^{3n} = 0",
        "(20/5.10) a^{3n}-b^{3n} = 0"]

if __name__ == "__main__":
    sys.exit(run({k: CLAIMS[k] for k in WANT}, PRIMES))
