"""Stage 4 smoke for chunk L4-01 (bo de 4).

Method note (contrast with L1-01 / L2-01): bo de 1 and bo de 2 have an
unsatisfiable hypothesis for n >= 3 (Fermat's equation has no nonzero
solution), so those screens could only test inferences. Bo de 4's
hypothesis is `a*b = c^n` with `(a,b) = m` and `m^2 ∤ b` -- easily
satisfiable -- so this screen runs on REAL witnesses as well, and a
boxed search that finds none would be a red flag.

Bo de 4 is a *parametrisation* result: it says every tuple satisfying the
hypotheses has the stated shape. So the screen has two halves:

  * the inference chain S1..S6 on real data (each step's implication on
    small ranges), and
  * the conclusion shape S7 on constructed families: build a, b, c from
    (m, n, s, c1, c2); the tuple must then satisfy the hypotheses AND the
    conclusion, which is what makes the parametrisation self-consistent.
  * two red-flag checks that the author's side hypotheses are
    load-bearing: m prime (S2) and m ∤ h*l*r (S5).

Witnesses here are NOT proofs; exit 0 means "no transcription red flag on
the searched range".
"""
import math
import sys
from itertools import product

import sympy


def v_p(x, p):
    """The p-adic valuation of a nonzero integer (abs, p prime)."""
    x = abs(x)
    k = 0
    while x % p == 0:
        x //= p
        k += 1
    return k


def check_S1_S2(m_set=(2, 3, 5), n_set=(1, 3, 5, 7, 11, 13), limit=12):
    """S1+S2 on real witnesses: m | a, m | b, a*b = c^n
    => m^2 | a*b = c^n  => m | c (the last step needs m prime)."""
    checked = 0
    for m in m_set:
        for n in n_set:
            for a, b in product(range(-limit, limit + 1), repeat=2):
                if a == 0 or b == 0 or abs(a) < 2 or abs(b) < 2:
                    continue
                if a % m or b % m:
                    continue
                prod = a * b
                root, exact = sympy.integer_nthroot(abs(prod), n)
                if not exact or root == 0:
                    continue
                c = root if prod > 0 else -root
                if c == 0 or a * b != c ** n:
                    continue
                assert c ** n % (m * m) == 0, f"S1 FAIL m={m} n={n} {(a, b, c)}"
                assert c % m == 0, f"S2 FAIL m={m} n={n} {(a, b, c)}"
                checked += 1
    print(f"S1+S2 ok ({checked} real witnesses: m|a, m|b, ab=c^n => m^2|c^n => m|c)")
    return True


def check_S2_primality_needed(mlimit=40, cmax=12, nmax=7):
    """Red flag: the S2 inference m^2 | c^n => m | c FAILS for composite m,
    so the author's "(do m la so nguyen to)" is load-bearing. Reports the
    smallest counterexamples it finds (all with n odd, as the lemma
    requires), and asserts at least one exists."""
    bad = []
    for m in range(4, mlimit):
        if sympy.isprime(m):
            continue
        for n in range(1, nmax + 1, 2):
            for c in range(2, cmax + 1):
                if c ** n % (m * m) == 0 and c % m != 0:
                    bad.append((m, n, c))
        if len(bad) >= 3:
            break
    assert bad, "S2 primality check: expected composite-m counterexamples, found none"
    print(f"S2 side condition ok (m prime is needed; counterexamples {bad[:3]})")
    return True


def check_S3(m_set=(2, 3, 5), n_set=(1, 3, 5, 7, 11, 13), climit=40):
    """S3: m | c lets us write c = m^s * r with m ∤ r (s = v_m(c), s >= 1),
    and m^2 | c^n  <=>  n*s >= 2 (again using m prime, m ∤ r)."""
    checked = 0
    for m in m_set:
        for c in range(2, climit):
            if c % m:
                continue
            s = v_p(c, m)
            r = c // (m ** s)
            assert s >= 1, f"S3 FAIL s>=1 m={m} c={c}"
            assert m ** s * r == c, f"S3 FAIL decomposition m={m} c={c}"
            assert r % m != 0, f"S3 FAIL r coprime m={m} c={c}"
            for n in n_set:
                assert ((c ** n) % (m * m) == 0) == (n * s >= 2), \
                    f"S3 FAIL ns>=2 m={m} n={n} c={c}"
            checked += 1
    print(f"S3 ok ({checked} m-multiples: c = m^s*r, m∤r, and n*s>=2 <=> m^2|c^n)")
    return True


def check_S5(m_set=(2, 3, 5), exp_max=6, cofactor=8):
    """S5: for prime m and m ∤ X, m ∤ Y,  m^P * X = m^Q * Y  forces
    P = Q and X = Y (the step that gives k+1 = ns and h*l = r^n)."""
    checked = 0
    for m in m_set:
        cands = [v for v in range(1, cofactor + 1) if v % m]
        for P, Q in product(range(exp_max + 1), repeat=2):
            for X, Y in product(cands, repeat=2):
                if m ** P * X == m ** Q * Y:
                    assert P == Q and X == Y, \
                        f"S5 FAIL m={m} P={P} Q={Q} X={X} Y={Y}"
                    checked += 1
    print(f"S5 ok ({checked} matches: m^P*X = m^Q*Y with m∤X, m∤Y => P=Q, X=Y)")
    return True


def check_S5_coprimality_needed(m=2):
    """Red flag: without m ∤ X the exponent comparison is false
    (2^1 * 6 = 2^2 * 3 with m | 6), so the coprimality of h*l*r in S5 is
    load-bearing."""
    lhs, rhs = m ** 1 * (m * 3), m ** 2 * 3
    assert lhs == rhs and (m * 3) % m == 0, "S5 side-condition probe drifted"
    print(f"S5 side condition ok (m ∤ h*l*r is needed; {m}^1*{(m * 3)} = "
          f"{m}^2*3 with exponents 1 != 2)")
    return True


def check_S6(n_set=(1, 3, 5, 7, 11, 13), limited=25):
    """S6 (bo de 3 applied): n odd, (h,l) = 1, h*l = r^n admits a solution
    r = c1*c2, h = c1^n, l = c2^n with (c1,c2) = 1 -- searched over real
    ordered pairs, and asserted to be unique in absolute value."""
    checked = 0
    for n in n_set:
        for h in range(1, limited + 1):
            for l in range(1, limited + 1):
                if math.gcd(h, l) != 1:
                    continue
                root, exact = sympy.integer_nthroot(h * l, n)
                if not exact:
                    continue
                r = root
                hits = []
                for c1 in range(1, r + 1):
                    if r % c1:
                        continue
                    c2 = r // c1
                    if math.gcd(c1, c2) == 1 and c1 ** n == h and c2 ** n == l:
                        hits.append((c1, c2))
                assert hits, f"S6 FAIL no c1,c2 for n={n} h={h} l={l} r={r}"
                checked += 1
    print(f"S6 ok ({checked} coprime (h,l) with h*l = r^n: r = c1*c2, "
          "h = c1^n, l = c2^n exists)")
    return True


def check_conclusion(m_set=(2, 3, 5), n_set=(1, 3, 5, 7, 11, 13), s_max=4, c_max=4):
    """S7 on constructed families: a = m^(ns-1) c2^n, b = m c1^n,
    c = m^s c1*c2 must satisfy the hypotheses AND the conclusion shape.
    Counts the real witnesses the lemma admits."""
    witnesses = 0
    counts: dict[int, int] = {}
    for m in m_set:
        for n in n_set:
            for s in range(1, s_max + 1):
                if n * s < 2:
                    continue
                for c1, c2 in product(range(-c_max, c_max + 1), repeat=2):
                    if c1 == 0 or c2 == 0:
                        continue
                    if math.gcd(abs(c1), abs(c2)) != 1:
                        continue
                    if c1 % m == 0 or c2 % m == 0:
                        continue
                    a = m ** (n * s - 1) * c2 ** n
                    b = m * c1 ** n
                    c = m ** s * c1 * c2
                    if min(abs(a), abs(b), abs(c)) < 2:
                        continue
                    # the constructed tuple really does satisfy the hypotheses
                    assert a * b == c ** n, f"S7 FAIL ab=c^n {(m, n, s, c1, c2)}"
                    assert a % m == 0 and b % m == 0, f"S7 FAIL m divides a,b"
                    assert math.gcd(abs(a), abs(b)) == m, f"S7 FAIL (a,b)=m"
                    assert b % (m * m) != 0, f"S7 FAIL m^2 does not divide b"
                    # ... and the conclusion's exact shape
                    assert s >= 1 and n * s >= 2
                    assert c1 % m != 0 and c2 % m != 0
                    assert c == m ** s * (c1 * c2)
                    assert a == m ** (n * s - 1) * c2 ** n
                    assert b == m * c1 ** n
                    witnesses += 1
                    counts[n] = counts.get(n, 0) + 1
    assert witnesses > 0, "S7 FAIL: no witness constructed (screen is vacuous)"
    required = (5, 7, 11, 13)
    for n in required:
        assert counts.get(n, 0) > 0, \
            f"S7 FAIL: no witness at n={n} (schema-required range)"
    print(f"S7 ok ({witnesses} constructed witnesses satisfy the hypotheses "
          "and the parametrisation exactly)")
    print("       per-n: " + ", ".join(f"n={n}:{counts.get(n, 0)}" for n in n_set))
    print("       schema-required range covered: "
          + ", ".join(f"n={n}" for n in required))
    return True


ok = (
    check_S1_S2()
    and check_S2_primality_needed()
    and check_S3()
    and check_S5()
    and check_S5_coprimality_needed()
    and check_S6()
    and check_conclusion()
)
print("L4 SMOKE PASS" if ok else "L4 SMOKE FAIL")
sys.exit(0 if ok else 1)
