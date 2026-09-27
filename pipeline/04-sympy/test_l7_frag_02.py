"""Smoke test for chunk L7-FRAG-02 (bổ đề 7: display (a) and (b), (c), (d)).

Real-instance screen: see l7_common for the witness search. Exit 0 = no
counterexample on the witnesses; the (a) identity must hold mod n², (b) mod n²,
(c) mod n, (d) mod n.
"""
import sys

from l7_common import CLAIMS, PRIMES, run

WANT = ["S0/5d c^{n(n-1)} = 1",
        "(a) a^{n2}+b^{n2}-c^{n2} = 0",
        "(b) c^n = a^n+b^n",
        "(c) c^{n(n-2)} = a^{..}+b^{..} mod n",
        "(d) a^n b^n = c^{2n} mod n"]

if __name__ == "__main__":
    sys.exit(run({k: CLAIMS[k] for k in WANT}, PRIMES))
