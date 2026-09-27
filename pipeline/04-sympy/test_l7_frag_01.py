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

# Factor forms the printed material mentions. The printed product's factors are
# (a^n - b^n)(c^n + a^n)(c^n + b^n); the printed proof's "chung minh tuong tu"
# line lists the three pairwise SUMS instead, so the difference instance
# a^n - b^n is the one Q-001 is about -- the tally below reports it separately
# rather than folding it into the product.
PRODUCT_FACTORS = ("a^n-b^n", "c^n+a^n", "c^n+b^n")
SUMS = ("a^n+b^n", "b^n+c^n")


def witnesses(n: int):
    found = []
    tally = {k: 0 for k in PRODUCT_FACTORS + SUMS}
    for a in range(1, n):
        for b in range(1, n):
            for c in range(1, n):
                if (pow(a, n, n * n) + pow(b, n, n * n) - pow(c, n, n * n)) % (n * n) != 0:
                    continue
                e = n * (n - 2)
                if (pow(a, e, n) + pow(b, e, n) - pow(c, e, n)) % n != 0:
                    continue
                A, B, C = pow(a, n, n), pow(b, n, n), pow(c, n, n)
                vals = {"a^n-b^n": (A - B) % n, "c^n+a^n": (C + A) % n,
                        "c^n+b^n": (C + B) % n, "a^n+b^n": (A + B) % n,
                        "b^n+c^n": (B + C) % n}
                for k, v in vals.items():
                    if v == 0:
                        tally[k] += 1
                prod = ((A - B) * (C + A) * (C + B)) % n
                found.append((a, b, c, prod))
    return found, tally


def main() -> int:
    bad = 0
    for n in PRIMES:
        w, tally = witnesses(n)
        n_bad = sum(1 for _, _, _, prod in w if prod == 0)
        print(f"n={n}: {len(w)} hypothesis-witnesses, {n_bad} with product==0 (mod n)")
        print(f"   zero factors mod n: {tally}")
        bad += n_bad
    if bad:
        print("COUNTEREXAMPLE FOUND — chunk is wrong, do not formalize")
        return 1
    print("smoke OK — no counterexample at small primes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
