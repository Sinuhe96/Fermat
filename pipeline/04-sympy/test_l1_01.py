"""Stage 4 smoke for chunk L1-01 (bổ đề 1).

Lemma 1 is pure gcd/divisibility logic (no modular arithmetic), so the
screen checks each author inference directly on small ranges instead of
searching for counterexamples to a statement:

  S1  (L1_reduce_coprime)  dividing a triple by its triple gcd leaves
                           triple gcd 1.
  S2+S3 (L1_step_S2_S3)    with d' = (u,v):  u^n + v^n = t^n  =>  d'^n | t^n.
  S4  (L1_step_S4)         d'^n | t^n  =>  d' | t.
  S5/S6 (L1_step_S5, S6)   if (u,v,t) = 1 then no d > 1 divides all three
                           (so any such d equals 1) — symmetric in the
                           three coordinates, hence covers the pairs
                           (u,v), (u,t), (v,t).
  vacuity                 for n in {5,7,11,13} no nonzero solution of
                           x^n + y^n = z^n exists in the searched box, so
                           the author's hypothesis (and every conclusion)
                           has no witness there — a red-flag screen only.

Witnesses below are NOT proofs; exit 0 only means "no transcription red
flag on the searched range".
"""
import math
import sys
from itertools import product


def gcd3(a, b, c):
    return math.gcd(math.gcd(abs(a), abs(b)), abs(c))


def iroot(m, n):
    """Integer n-th root of m >= 0, or None if m is not a perfect n-th power."""
    if m == 0:
        return 0
    lo, hi = 0, 1
    while hi ** n <= m:
        hi *= 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** n <= m:
            lo = mid
        else:
            hi = mid - 1
    return lo if lo ** n == m else None


def check_S1(limit=30):
    checked = 0
    for u0, v0, t0 in product(range(-limit, limit + 1), repeat=3):
        if u0 == 0 or v0 == 0 or t0 == 0:
            continue
        d = gcd3(u0, v0, t0)
        if gcd3(u0 // d, v0 // d, t0 // d) != 1:
            print(f"S1 FAIL at {(u0, v0, t0)}")
            return False
        checked += 1
    print(f"S1 ok ({checked} nonzero triples reduce to triple gcd 1)")
    return True


def check_S2_S3(n_range=(1, 2), limit=40):
    """S2+S3 needs instances of u^n + v^n = t^n; none exist for n >= 3, so the
    inference is screened on n = 1, 2 where solutions exist."""
    checked = 0
    for n in n_range:
        for u in range(-limit, limit + 1):
            for v in range(-limit, limit + 1):
                if u == 0 or v == 0:
                    continue
                s = u ** n + v ** n
                r = iroot(abs(s), n)
                if r is None or r == 0:
                    continue
                t = r if (n % 2 == 1 and s > 0) or n % 2 == 0 else -r
                if n % 2 == 0:
                    t = r
                if t ** n != s:
                    continue
                d = math.gcd(abs(u), abs(v))
                if pow(t, n) % pow(d, n) != 0:
                    print(f"S2+S3 FAIL at n={n} u={u} v={v} t={t} d={d}")
                    return False
                checked += 1
    print(f"S2+S3 ok ({checked} solutions: (u,v)^n divides t^n)")
    return True


def check_S4(n_range=(1, 2, 3, 4, 5), dmax=40, tmax=40):
    checked = 0
    for n in n_range:
        for d in range(1, dmax + 1):
            for t in range(-tmax, tmax + 1):
                if t == 0:
                    continue
                if pow(t, n) % pow(d, n) == 0 and t % d != 0:
                    print(f"S4 FAIL at n={n} d={d} t={t}")
                    return False
                checked += 1
    print(f"S4 ok ({checked} (n,d,t) cases: d^n | t^n => d | t)")
    return True


def check_S5(limit=12):
    """(u,v,t) = 1 forbids any common divisor d > 1; S5 uses this at
    d = (u,v), d = (u,t), d = (v,t)."""
    checked = 0
    for u, v, t in product(range(-limit, limit + 1), repeat=3):
        if gcd3(u, v, t) != 1:
            continue
        for d in range(2, limit * limit + 2):
            if u % d == 0 and v % d == 0 and t % d == 0:
                print(f"S5 FAIL at {(u, v, t)} with d={d}")
                return False
        checked += 1
    print(f"S5/S6 ok ({checked} triples with (u,v,t) = 1 have no common divisor > 1)")
    return True


def check_vacuity(n_set=(5, 7, 11, 13), limit=40):
    solutions = 0
    for n in n_set:
        for x in range(-limit, limit + 1):
            for y in range(-limit, limit + 1):
                if x == 0 or y == 0:
                    continue
                s = x ** n + y ** n
                r = iroot(abs(s), n)
                if r is None or r == 0:
                    continue
                z = r if s > 0 else -r
                if z ** n != s:
                    continue
                solutions += 1
                print(f"  witness n={n} x={x} y={y} z={z}")
                if gcd3(x, y, z) != 1 or (math.gcd(abs(x), abs(y)) != 1
                                          or math.gcd(abs(x), abs(z)) != 1
                                          or math.gcd(abs(y), abs(z)) != 1):
                    d = gcd3(x, y, z)
                    if gcd3(x // d, y // d, z // d) != 1:
                        print(f"vacuity-branch FAIL at {(x, y, z)}")
                        return False
    print(f"vacuity ok (n in {n_set}, |x|,|y| <= {limit}: {solutions} solutions found)")
    return True


ok = (check_S1() and check_S2_S3() and check_S4() and check_S5()
      and check_vacuity())
print("L1 SMOKE PASS" if ok else "L1 SMOKE FAIL")
sys.exit(0 if ok else 1)
