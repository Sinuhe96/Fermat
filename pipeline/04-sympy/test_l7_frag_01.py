"""Smoke test for chunk L7-FRAG-01 (Lemma 7 fragment, pilot).

Checks the *hypotheses are satisfiable* for small primes and records the
shape of the conclusion — BEFORE any Lean proof is attempted.

Strategy: brute-force small a,b,c in [1, n-1] for n in {5,7,11,13} and
report triples satisfying:
    a^n + b^n - c^n == 0 (mod n^2)
    a^{n(n-2)} + b^{n(n-2)} - c^{n(n-2)} == 0 (mod n)
For each such triple, check whether (a^n-b^n)(c^n+a^n)(c^n+b^n) == 0 (mod n).

- If NO triple satisfies the hypotheses: hypotheses may be vacuous at small
  n (fine — the test still passes, it just reports 0 witnesses).
- If a triple satisfies hypotheses AND the conclusion product == 0 (mod n):
  the chunk is WRONG (transcription error or false lemma) — STOP, fix the
  chunk, never start the Lean proof.

Exit 0 = smoke passed (no counterexample). Exit 1 = counterexample found.
"""
import sys

PRIMES = [5, 7, 11, 13]


def witnesses(n: int):
    found = []
    for a in range(1, n):
        for b in range(1, n):
            for c in range(1, n):
                if (pow(a, n, n * n) + pow(b, n, n * n) - pow(c, n, n * n)) % (n * n) != 0:
                    continue
                e = n * (n - 2)
                if (pow(a, e, n) + pow(b, e, n) - pow(c, e, n)) % n != 0:
                    continue
                prod = (
                    (pow(a, n, n) - pow(b, n, n))
                    * (pow(c, n, n) + pow(a, n, n))
                    * (pow(c, n, n) + pow(b, n, n))
                ) % n
                found.append((a, b, c, prod))
    return found


def main() -> int:
    bad = 0
    for n in PRIMES:
        w = witnesses(n)
        n_bad = sum(1 for _, _, _, prod in w if prod == 0)
        print(f"n={n}: {len(w)} hypothesis-witnesses, {n_bad} with product==0 (mod n)")
        bad += n_bad
    if bad:
        print("COUNTEREXAMPLE FOUND — chunk is wrong, do not formalize")
        return 1
    print("smoke OK — no counterexample at small primes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
