"""Stage 4 smoke for chunk L3-01 (bo de 3).

Lemma 3: a*b = c^n with (a,b) = 1 and n odd positive splits into coprime
nth-power factors: exists c1, c2 nonzero, (c1,c2) = 1, c = c1*c2,
a = c1^n, b = c2^n.

Unlike L1/L2 (whose hypotheses are the FLT equation and therefore
vacuous for n >= 3), Lemma 3's hypotheses are satisfiable for EVERY odd
n (a = c1^n, b = c2^n, c = c1*c2). So every author step is screened on
real instances, not vacuously:

  S0    gcd division: with c'_1 = (a,c), the quotients a/c'_1 and
        c/c'_1 are coprime.
  S1    substitution: c'_1*a_1*b = c'_1^n * c'_2^n.
  S2    cancellation: a_1*b = c'_1^(n-1) * c'_2^n.
  S3    b divides c'_1^(n-1) * c'_2^n.
  S4    (c'_1,b) = 1 and c'_2^n = k*b with integer k != 0.
  S5    cancellation of b: a_1 = k*c'_1^(n-1).
  S6    powering: a_1^n = k^n * c'_1^(n(n-1)).
  S7    k divides a_1^n.
  S8    k divides c'_2^n.
  S9    (a_1,c'_2) = 1 gives (a_1^n, c'_2^n) = 1.
  S10   k divides both coprime powers, so |k| = 1.
  S11   c_1 = k*c'_1, c_2 = k*c'_2 are nonzero, coprime, and satisfy
        c = c_1*c_2, a = c_1^n, b = c_2^n  (uses |k| = 1 and n odd).
  statement  the final conclusion holds on every instance found in the
        boxed search (nth-root witnesses constructed and verified).

Instances come from two generators: (i) structured coprime pairs
(c1, c2) lifted to a = c1^n, b = c2^n, and (ii) a natural box over
coprime (a, b) whose product is an exact nth power. n ranges over
{1, 3, 5, 7, 11, 13}, which includes the schema-required
{5, 7, 11, 13}.

oddness sanity: for even n the statement is FALSE (a = -4, b = -9,
c = 6, n = 2 satisfies the hypotheses but a is no square), so the
author's "n la so nguyen duong le" hypothesis is load-bearing; the
screen exhibits that counterexample as a checker sanity, not as an
author claim.

Witnesses below are NOT proofs; exit 0 only means "no transcription red
flag on the searched range".
"""

import math
import sys

import sympy

N_SET = (1, 3, 5, 7, 11, 13)


def signed_iroot(p, n):
    """Exact integer n-th root of p, or None. Only meaningful for odd n
    (for even n: negative p has no root)."""
    if n % 2 == 0:
        if p < 0:
            return None
        r, exact = sympy.integer_nthroot(p, n)
        return int(r) if exact else None
    neg = p < 0
    r, exact = sympy.integer_nthroot(abs(p), n)
    if not exact:
        return None
    return -int(r) if neg else int(r)


def run_chain(a, b, c, n):
    """Run the author's S0-S11 chain on one instance of the statement
    hypotheses. AssertionError at step k = first failing author step."""
    # statement hypotheses
    assert n >= 1 and n % 2 == 1, "hyps: n positive odd"
    assert a != 0 and b != 0 and c != 0, "hyps: a,b,c nonzero"
    assert a * b == c ** n, "hyps: a*b = c^n"
    assert math.gcd(abs(a), abs(b)) == 1, "hyps: (a,b) = 1"

    # S0: divide a and c by c'_1 = (a,c); quotients coprime
    c1p = math.gcd(abs(a), abs(c))
    a1 = a // c1p
    c2p = c // c1p
    assert math.gcd(abs(a1), abs(c2p)) == 1, "S0"

    # S1: substitution
    assert c1p * a1 * b == c1p ** n * c2p ** n, "S1"

    # S2: cancel c'_1
    assert a1 * b == c1p ** (n - 1) * c2p ** n, "S2"

    # S3: divisibility
    assert (c1p ** (n - 1) * c2p ** n) % b == 0, "S3"

    # S4: (c'_1,b) = 1, then c'_2^n = k*b with k != 0
    assert math.gcd(abs(c1p), abs(b)) == 1, "S4: (c'_1,b) = 1"
    assert (c2p ** n) % b == 0, "S4: b | c'_2^n"
    k = (c2p ** n) // b
    assert c2p ** n == k * b, "S4: c'_2^n = k*b"
    assert k != 0, "S4: k nonzero"

    # S5: cancel b
    assert a1 == k * c1p ** (n - 1), "S5"

    # S6: powering
    assert a1 ** n == k ** n * c1p ** (n * (n - 1)), "S6"

    # S7: k | a_1^n
    assert (a1 ** n) % k == 0, "S7"

    # S8: k | c'_2^n
    assert (c2p ** n) % k == 0, "S8"

    # S9: coprime powers
    assert math.gcd(abs(a1 ** n), abs(c2p ** n)) == 1, "S9"

    # S10: k divides both, so |k| = 1
    assert abs(k) == 1, "S10"

    # S11: the constructed witnesses
    c_1 = k * c1p
    c_2 = k * c2p
    assert c_1 != 0 and c_2 != 0, "S11: nonzero"
    assert math.gcd(abs(c_1), abs(c_2)) == 1, "S11: (c_1,c_2) = 1"
    assert c == c_1 * c_2, "S11: c = c_1*c_2"
    assert a == c_1 ** n, "S11: a = c_1^n"
    assert b == c_2 ** n, "S11: b = c_2^n"
    return True


def check_statement(a, b, c, n):
    """The conclusion, with witnesses built by exact nth roots."""
    c_1 = signed_iroot(a, n)
    c_2 = signed_iroot(b, n)
    assert c_1 is not None, "statement: a is not an exact nth power"
    assert c_2 is not None, "statement: b is not an exact nth power"
    assert c_1 != 0 and c_2 != 0, "statement: nonzero"
    assert math.gcd(abs(c_1), abs(c_2)) == 1, "statement: coprime"
    assert c == c_1 * c_2, "statement: c = c_1*c_2"
    return True


def check_structured(n_set=N_SET, R=12):
    """Generator (i): coprime pairs (c1, c2) lifted to a = c1^n."""
    count = 0
    for n in n_set:
        for c1 in range(-R, R + 1):
            if c1 == 0:
                continue
            for c2 in range(-R, R + 1):
                if c2 == 0:
                    continue
                if math.gcd(abs(c1), abs(c2)) != 1:
                    continue
                a, b, c = c1 ** n, c2 ** n, c1 * c2
                run_chain(a, b, c, n)
                check_statement(a, b, c, n)
                count += 1
    print(f"structured ok ({count} instances, n in {n_set}: S0-S11 chain "
          f"+ statement witnesses)")
    return True


def check_box(n_set=N_SET, B=30):
    """Generator (ii): natural box over coprime (a, b) whose product is
    an exact nth power. Exercises instances not built from nth powers
    by hand."""
    count = 0
    for n in n_set:
        for a in range(-B, B + 1):
            if a == 0:
                continue
            for b in range(-B, B + 1):
                if b == 0:
                    continue
                if math.gcd(abs(a), abs(b)) != 1:
                    continue
                c = signed_iroot(a * b, n)
                if c is None or c == 0:
                    continue
                run_chain(a, b, c, n)
                check_statement(a, b, c, n)
                count += 1
    print(f"box ok ({count} boxed instances with a*b = c^n, n in {n_set}: "
          f"S0-S11 chain + statement witnesses)")
    return True


def check_oddness():
    """Even-n counterexample: the hypotheses hold, the conclusion fails.
    Documents that the author's oddness hypothesis is load-bearing."""
    a, b, c, n = -4, -9, 6, 2
    assert a * b == c ** n, "even-n hypotheses: a*b = c^n"
    assert math.gcd(abs(a), abs(b)) == 1, "even-n hypotheses: (a,b) = 1"
    assert a != 0 and b != 0 and c != 0, "even-n hypotheses: nonzero"
    assert signed_iroot(a, n) is None, "even-n: a is no square"
    print("oddness sanity ok (even-n counterexample a=-4, b=-9, c=6, "
          "n=2: conclusion fails as expected)")
    return True


def main():
    try:
        ok = check_structured() and check_box() and check_oddness()
    except AssertionError as e:
        print(f"L3 SMOKE FAIL at step {e}")
        return 1
    print("L3 SMOKE PASS" if ok else "L3 SMOKE FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
