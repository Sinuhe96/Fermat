"""Smoke test for chunk L7-FRAG-04 (bổ đề 7: (18) and (22')).

Real-instance screen: see l7_common. Exit 0 = no counterexample.
"""
import sys

from l7_common import CLAIMS, PRIMES, run

WANT = ["(18) a^{2n}+b^n c^n = 0",
        "(18) b^{2n}+a^n c^n = 0",
        "(18) c^{2n}-a^n b^n = 0",
        "(22') a^{n(n-2)}+b^{n(n-2)}-c^{n(n-2)} = 0"]

if __name__ == "__main__":
    sys.exit(run({k: CLAIMS[k] for k in WANT}, PRIMES))
