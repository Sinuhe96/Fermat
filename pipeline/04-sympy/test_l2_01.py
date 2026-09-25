"""Stage 4 smoke for chunk L2-01 (bo de 2).

Lemma 2 is a pure exponent-identity / contrapositive step (no modular
arithmetic), so the screen checks the author's inferences directly:

  S1  (L2_step_S1)  coordinate identity  (u^k)^n = u^(k*n)  on a box, and
                    nonzero coordinates stay nonzero after exponentiation.
  S2  (contrapositive direction used by S2/S3): every integer witness of
      x^(k*n) + y^(k*n) = z^(k*n)  (of the searched type: z as a computed
      n-th power) yields a witness (u^k, v^k, t^k) of x^n + y^n = z^n.
  vacuity  for n in {5,7,11,13}, k in {2,3,5} no nonzero solution of
           x^n + y^n = z^n exists in the searched box, so the author's
           hypothesis (and every conclusion of the lemma) has no witness
           there -- a red-flag screen only.

Witnesses below are NOT proofs; exit 0 only means "no transcription red
flag on the searched range".
"""
import math
import sys
from itertools import product

import sympy


def check_S1(n_range=(1, 2, 3, 4, 5), k_range=(1, 2, 3, 7), limit=25):
    """The display step's content: (u^k)^n = u^(k*n) coordinate-wise, and
    u != 0 implies u^k != 0."""
    checked = 0
    for n in n_range:
        for k in k_range:
            for u in range(-limit, limit + 1):
                if u == 0:
                    continue
                assert (u ** k) ** n == u ** (k * n), f"S1 FAIL at n={n} k={k} u={u}"
                assert u ** k != 0, f"S1 FAIL nonzero at n={n} k={k} u={u}"
                checked += 1
    print(f"S1 ok ({checked} (n,k,u) cases: (u^k)^n = u^(k*n), nonzero preserved)")
    return True


def find_solutions(exp, limit):
    """Return triples (u,v,t) with u,v,t != 0 and u^exp + v^exp = t^exp,
    |u|,|v| <= limit, t computed as the integer exp-th root of u^exp+v^exp."""
    sols = []
    for u, v in product(range(-limit, limit + 1), repeat=2):
        if u == 0 or v == 0:
            continue
        s = u ** exp + v ** exp
        if s == 0:
            if exp % 2 == 1 and u != 0 and v != 0:
                # u^exp + v^exp = 0 with t = 0 is not allowed (nonzero t)
                continue
        r = sympy.integer_nthroot(abs(s), exp)
        if not r[1] or r[0] == 0:
            continue
        t = r[0] if s > 0 else -r[0]
        if t == 0:
            continue
        if u ** exp + v ** exp == t ** exp:
            sols.append((u, v, t))
    return sols


def check_S2(limit=30):
    """The contrapositive step (author S2): a witness of the k*n equation
    must give a witness of the n equation via (u,v,t) -> (u^k, v^k, t^k).

    The transformation (u^k)^n = u^(k*n) does not depend on n, so we can
    exercise it on REAL witnesses by taking n = 1 (for which the equation
    has plenty of solutions); for n >= 3 the k*n equation has no nonzero
    integer solution at all in any box, which is the vacuity red-flag
    covered by check_vacuity."""
    checked = 0
    n = 1
    for k in (1, 2, 3, 5):
        exp = k * n
        for (u, v, t) in find_solutions(exp, limit):
            if u ** k == 0 or v ** k == 0 or t ** k == 0:
                print(f"S2 FAIL nonzero at n={n} k={k} {(u, v, t)}")
                return False
            if (u ** k) ** n + (v ** k) ** n != (t ** k) ** n:
                print(f"S2 FAIL at n={n} k={k} {(u, v, t)}")
                return False
            checked += 1
    print(f"S2 ok ({checked} witnesses of x^(kn)+y^(kn)=z^(kn) lift to x^n+y^n=z^n)")
    return True


def check_vacuity(n_set=(5, 7, 11, 13), k_set=(2, 3, 5), limit=40):
    """For n >= 3 no nonzero integer solution of x^n + y^n = z^n exists in
    the box, so the author's hypothesis has no witness there: Lemma 2 is
    vacuous on this range. Also verifies the contrapositive consistency:
    no boxed witness for the k*n equation either."""
    bad = 0
    for n in n_set:
        for k in k_set:
            for u, v in product(range(-limit, limit + 1), repeat=2):
                if u == 0 or v == 0:
                    continue
                s = u ** (n * k) + v ** (n * k)
                if s == 0:
                    continue
                r = sympy.integer_nthroot(abs(s), n * k)
                if r[1] and r[0] != 0:
                    t = r[0] if s > 0 else -r[0]
                    if t != 0 and not (u == 0 or v == 0 or t == 0):
                        bad += 1
                        print(f"vacuity witness n={n} k={k} {(u, v, t)}")
    if bad:
        print("vacuity FAIL: unexpected witness of the k*n equation")
        return False
    print(f"vacuity ok (n in {n_set}, k in {k_set}, |u|,|v| <= {limit}: 0 candidates)")
    return True


ok = (check_S1() and check_S2() and check_vacuity())
print("L2 SMOKE PASS" if ok else "L2 SMOKE FAIL")
sys.exit(0 if ok else 1)