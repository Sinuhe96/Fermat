"""Smoke test for the section assembly L7-ASM (bổ đề 7 in full).

The assembly states the whole printed conclusion list, so the screen checks
every one of its conjuncts on the same real witnesses — the section-level
screen AGENTS.md asks for when the section states a conclusion its leaves do
not already screen (here: the conjunction itself, plus (22)/(21), which the
main proof cites together with (17)).
"""
import sys

from l7_common import CLAIMS, PRIMES, run

WANT = list(CLAIMS)  # every claim, including "n = 1 (mod 6)"

if __name__ == "__main__":
    sys.exit(run({k: CLAIMS[k] for k in WANT}, PRIMES))
