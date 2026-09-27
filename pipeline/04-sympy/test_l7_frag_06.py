"""Smoke test for chunk L7-FRAG-06 (bổ đề 7: (21) and (22)).

Real-instance screen: see l7_common. Exit 0 = no counterexample.
"""
import sys

from l7_common import CLAIMS, PRIMES, run

WANT = ["(21) a^{n(n-4)}+c^{n(n-4)} = 0",
        "(21) b^{n(n-4)}+c^{n(n-4)} = 0",
        "(21) a^{n(n-4)}-b^{n(n-4)} = 0",
        "(22) a^{n(n-3)}+b^{n(n-3)}+c^{n(n-3)} = 0"]

if __name__ == "__main__":
    sys.exit(run({k: CLAIMS[k] for k in WANT}, PRIMES))
