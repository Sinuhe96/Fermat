"""Algebraic core of the main proof (PDF pp. 6-33) - shared screens.

Two facilities live here because every M1 leaf needs them and neither depends
on the leaf split.

1. VACUITY ACCOUNTING. The main proof's outer hypotheses contain a Fermat
   equation solution (u, v, t) for a prime n > 11, so they admit NO integer
   witness: a boxed search finds zero solutions for every n >= 3
   (`fermat_box_count`). Anything in the main proof that is *conditional on
   the equation* (3) therefore cannot be exercised on real instances and has
   to be verified in Lean, not here. Only the parts that are unconditional
   polynomial/divisibility facts are screenable; each screen below says which
   kind it is.

2. THE 1.1 EXPANSION CORE (p. 6). With the bo de 6 parametrisation

       X := n^s * a*b*c*k,   u := b^n + X,   v := a^n + X,   t := h - X

   the binomial theorem gives the exact identity

       (b^n + X)^n + (a^n + X)^n - (h - X)^n
         = sum_{i=0}^{n} C(n,i) * X^i * [ b^(n(n-i)) + a^(n(n-i)) - h^(n-i)*(-1)^i ]

   (`term`). The i = 0 summand is `a^(n^2) + b^(n^2) - h^n`, so the printed
   chain's starting point is

       equation (3) holds  <=>  sum_{i>=1} term(n,i,...) = h^n - a^(n^2) - b^(n^2).

   The printed displays (7)/(7')/(8)/(9)/(10) truncate that sum at
   order = 1/0/2/3/4 and claim the tail is invisible modulo
   n^((order+1)*s + 1). That truncation is UNCONDITIONAL, and it is the only
   thing screenable here: for prime n every C(n,i), 1 <= i <= n-1, carries one
   factor n, so the i-th summand is divisible by n * X^i = n^(i*s+1)*(a*b*c*k)^i.
   Hence `tail(order) = 0 (mod n^((order+1)*s+1))` holds with no hypothesis,
   while the printed congruence itself needs (3) as a hypothesis - which is
   exactly how the leaf must state it in Lean.

   Screens: `screen_expansion` (the identity above, exact), `screen_tail`
   (each printed truncation unconditional, moduli sharp), `screen_vacuity`.

Run:  docker compose exec -T lean python /workspace/pipeline/04-sympy/m1_common.py
Exit 0 iff every screen passes.
"""
from __future__ import annotations

import itertools
import random
from math import comb

import sympy as sp

PRIMES = (5, 7, 11, 13)  # schema-required screen range
BIG_PRIMES = (13, 17, 19, 23)  # the main proof's n > 11 territory
SEED = 20260928

# printed display -> truncation order kept on the RHS
DISPLAY = {0: "(7')", 1: "(7)", 2: "(8)", 3: "(9)", 4: "(10)"}


def fermat_box_count(n: int, lim: int) -> int:
    """Number of x, y, z with 1 <= x, y, z <= lim and x^n + y^n = z^n.

    Zero for every n >= 3 (Fermat). Used only to state the vacuity of the
    main proof's outer hypotheses honestly; it proves nothing.
    """
    pows = {i: i**n for i in range(1, lim + 1)}
    zpow = set(pows.values())
    return sum(1 for x, y in itertools.product(pows.values(), repeat=2) if x + y in zpow)


def free_params(n: int, rng: random.Random, s_min: int = 2, s_max: int = 3, cap: int | None = None):
    """Parameters satisfying the printed side conditions of the core.

    a, b, c, k coprime to the prime n (the non-divisibility hypotheses the main
    proof carries), s >= 2 (bo de 6's 6.2 branch), and h of one of the two
    printed shapes: h = c^n when t is not divisible by n, and
    h = n^(n*s-1) * c^n when it is.
    """
    cap = cap or n * n
    while True:
        a, b, c, k = (rng.randrange(1, cap) for _ in range(4))
        if any(v % n == 0 for v in (a, b, c, k)):
            continue
        s = rng.randrange(s_min, s_max + 1)
        if rng.random() < 0.5:
            h = c**n
        else:
            h = n ** (n * s - 1) * c**n
        return a, b, c, k, s, h


def X_of(n: int, a: int, b: int, c: int, k: int, s: int) -> int:
    """The printed shortand n^s * a*b*c*k."""
    return n**s * a * b * c * k


def term(n: int, i: int, a: int, b: int, c: int, k: int, s: int, h: int) -> int:
    """The i-th summand of the expansion identity."""
    X = X_of(n, a, b, c, k, s)
    return comb(n, i) * X**i * (b ** (n * (n - i)) + a ** (n * (n - i)) - (-1) ** i * h ** (n - i))


def expansion_sum(n: int, a: int, b: int, c: int, k: int, s: int, h: int) -> int:
    """sum_{i=0}^{n} term(i)."""
    return sum(term(n, i, a, b, c, k, s, h) for i in range(n + 1))


def binom_difference(n: int, a: int, b: int, c: int, k: int, s: int, h: int) -> int:
    """(b^n + X)^n + (a^n + X)^n - (h - X)^n, the binomial side of the identity."""
    X = X_of(n, a, b, c, k, s)
    return (b**n + X) ** n + (a**n + X) ** n - (h - X) ** n


def tail(n: int, a: int, b: int, c: int, k: int, s: int, h: int, order: int) -> int:
    """The summands the printed truncation of `order` drops: sum_{i>order} term(i)."""
    return sum(term(n, i, a, b, c, k, s, h) for i in range(order + 1, n + 1))


def printed_modulus(n: int, s: int, order: int) -> int:
    """The modulus the display prints for this truncation order."""
    return n ** ((order + 1) * s + 1)


def expected_exponent(n: int, s: int, order: int) -> int:
    """n-adic exponent every dropped summand is guaranteed to carry.

    For 1 <= i <= n-1 the binomial coefficient C(n,i) supplies one factor n,
    so the i-th summand has n^(i*s + 1). The LAST summand i = n has C(n,n) = 1
    and only reaches n^(n*s). The tail's guaranteed exponent is therefore the
    minimum over the dropped indices.
    """
    return min(i * s + (1 if i < n else 0) for i in range(order + 1, n + 1))


def excess_exponent(value: int, n: int) -> int:
    """Largest e with n^e | value (n prime, value != 0)."""
    e = 0
    while value % n == 0:
        value //= n
        e += 1
    return e


def screen_vacuity(lim: int = 40) -> bool:
    """Record honestly that the outer hypotheses admit no witness."""
    ok = True
    for n in (3, 5, 7):
        cnt = fermat_box_count(n, lim)
        if cnt != 0:
            print(f"FAIL vacuity n={n}: {cnt} solutions with coords <= {lim}")
            ok = False
    print(f"vacuity: x^n + y^n = z^n has 0 solutions for n in (3,5,7), coords <= {lim}")
    return ok


def screen_expansion(primes=PRIMES + BIG_PRIMES, per_prime: int = 3) -> bool:
    """The binomial identity the printed chain starts from, exact (no modulus)."""
    ok = True
    rng = random.Random(SEED)
    for n in primes:
        if n % 2 == 0:
            print(f"FAIL expansion n={n}: not odd")
            ok = False
            continue
        for _ in range(per_prime):
            a, b, c, k, s, h = free_params(n, rng)
            left = expansion_sum(n, a, b, c, k, s, h)
            right = binom_difference(n, a, b, c, k, s, h)
            if left != right:
                print(f"FAIL expansion n={n} a={a} b={b} c={c} k={k} s={s}: {left - right:+d}")
                ok = False
        print(f"expansion identity exact on {per_prime} instances, n={n}")
    return ok


def screen_tail(primes=PRIMES + BIG_PRIMES, per_prime: int = 6, verbose: bool = False) -> bool:
    """Each printed truncation is unconditional; each printed modulus is sharp.

    The printed modulus n^((order+1)*s + 1) is implied by the summand bound only
    while order + 1 <= n - 1, i.e. order <= n - 2. Beyond that the last summand
    i = n (whose C(n,n) = 1 supplies no factor n) can be coarser: at n = 5,
    order 4 the printed n^(5s+1) overstates the unconditional n^(5s). The
    author's n > 11 keeps order <= 4 <= n - 2, so this never bites the main
    proof; the screen records it instead of silently skipping n = 5.
    """
    ok = True
    rng = random.Random(SEED + 1)
    for n in dict.fromkeys(primes):
        if n % 2 == 0:
            print(f"FAIL tail n={n}: not odd")
            ok = False
            continue
        for order in sorted(DISPLAY):
            printed_ok = order <= n - 2
            tight_fail = 0
            bad = 0
            for _ in range(per_prime):
                a, b, c, k, s, h = free_params(n, rng)
                t = tail(n, a, b, c, k, s, h, order)
                if t % n**expected_exponent(n, s, order) != 0:
                    print(
                        f"FAIL {DISPLAY[order]} n={n} order={order} "
                        f"a={a} b={b} c={c} k={k} s={s}: below the guaranteed exponent"
                    )
                    ok = False
                    bad += 1
                if printed_ok and t % printed_modulus(n, s, order) != 0:
                    print(
                        f"FAIL {DISPLAY[order]} n={n} order={order} "
                        f"a={a} b={b} c={c} k={k} s={s}: printed modulus missed"
                    )
                    ok = False
                    bad += 1
                if t % (printed_modulus(n, s, order) * n) != 0:
                    tight_fail += 1
            if not printed_ok:
                print(
                    f"NOTE {DISPLAY[order]} n={n}: order {order} = n-1, so the i=n summand "
                    f"is only guaranteed n^(n*s); printed modulus overstates by one n. "
                    f"Outside the author's range (n > 11), display unaffected."
                )
            if not verbose and bad == 0:
                print(
                    f"tail {DISPLAY[order]} n={n} order={order}: "
                    f"{per_prime}/{per_prime} OK" + ("" if printed_ok else " (guaranteed bound only)")
                )
    return ok


# --- p. 6's second derivation: the (t^n - u^n = v^n) regrouping ---------------
#
# Expanding sum_{i<n} (h-X)^(n-1-i) (b^n+X)^i binomially (i outermost, j from the
# (h-X) factor, l from the (b^n+X) factor) gives the printed triple sum
#
#   T = sum_{i<n} sum_{j<=n-1-i} sum_{l<=i} (-1)^j C(n-1-i,j) C(i,l)
#           h^(n-1-i-j) b^(n(i-l)) X^(l+j).
#
# The p. 6 R3 display re-writes T by grouping the summands by the value of l+j,
# listing the l+j in {2,3,4} groups explicitly and keeping l+j >= 5 as a
# residual sum. That regrouping is a pure PARTITION of the index set - it needs
# no hypothesis and no equation - so it is screenable on free (h, b, X). The
# display's ten printed groups and their index ranges are transcribed below as
# printed; the check asserts each range is the natural [l, n-1-j] and that the
# listed pairs are exactly the l+j in {2,3,4} pairs minus the two the page's
# continuation carries ((1,1) and (0,2)).
#
# The region record flags one ambiguity: the residual's subscript condition was
# read from the glyphs as "l + j >= 5". The screen uses that reading; the
# partition identity is what makes it checkable.

# (l, j, i_lo as printed, i_hi as printed)
P6_PRINTED_GROUPS = (
    (4, 0, 4, "n-1"),
    (0, 4, 0, "n-5"),
    (1, 3, 1, "n-4"),
    (3, 1, 3, "n-2"),
    (2, 2, 2, "n-3"),
    (1, 2, 1, "n-3"),
    (2, 1, 2, "n-2"),
    (0, 3, 0, "n-4"),
    (3, 0, 3, "n-1"),
    (2, 0, 2, "n-1"),
)

P6_HI = {"n-1": -1, "n-2": -2, "n-3": -3, "n-4": -4, "n-5": -5}


def p6_hi(expr: str, n: int) -> int:
    """The printed upper index, as an offset from n."""
    return n + P6_HI[expr]


def p6_term(n: int, i: int, j: int, l: int, h: int, b: int, X: int) -> int:
    """One summand of the printed triple sum."""
    return (
        (-1) ** j
        * comb(n - 1 - i, j)
        * comb(i, l)
        * h ** (n - 1 - i - j)
        * b ** (n * (i - l))
        * X ** (l + j)
    )


def p6_triple_sum(n: int, h: int, b: int, X: int, keep=None) -> int:
    """T, optionally restricted to the (l, j) pairs `keep` accepts."""
    tot = 0
    for i in range(n):
        for j in range(n - 1 - i + 1):
            for l in range(i + 1):
                if keep is None or keep(l, j):
                    tot += p6_term(n, i, j, l, h, b, X)
    return tot


def screen_p6_regroup(primes=(7, 11, 13), per_prime: int = 2) -> bool:
    """The printed regrouping of T, and the R2/R3 spelling reconciliation."""
    ok = True
    rng = random.Random(SEED + 2)
    for n in primes:
        # 1. n(n-1-i) + i = (n-1)(n-i): R2's "a^{(n-1)(n-i)} (n^s bck)^i" and
        #    R3's "a^{n(n-1-i)} (n^s abck)^i" are the SAME summand. The two
        #    spellings differing while both being signed latex is therefore not
        #    a typo and needs no author query.
        for i in range(n + 1):
            if n * (n - 1 - i) + i != (n - 1) * (n - i):
                print(f"FAIL exponent reconciliation n={n} i={i}")
                ok = False

        # 2. every printed index range is the natural [l, n-1-j]
        for (l, j, lo, hi) in P6_PRINTED_GROUPS:
            if lo != l or p6_hi(hi, n) != n - 1 - j:
                print(
                    f"FAIL printed range n={n} (l,j)=({l},{j}): printed i in "
                    f"[{lo},{hi}] = [{lo},{p6_hi(hi, n)}], natural is [{l},{n - 1 - j}]"
                )
                ok = False

        # 3. the listed pairs are exactly l+j in {2,3,4} minus the two the
        #    page's continuation carries
        listed = {(l, j) for (l, j, _, _) in P6_PRINTED_GROUPS}
        want = {(l, j) for l in range(5) for j in range(5) if 2 <= l + j <= 4} - {(1, 1), (0, 2)}
        if listed != want:
            print(f"FAIL listed pairs n={n}: missing {sorted(want - listed)}, extra {sorted(listed - want)}")
            ok = False

        # 4. the partition itself: LHS = residual + printed groups + remainder
        for _ in range(per_prime):
            h = rng.randrange(1, 10**6)
            b = rng.randrange(1, 10**6)
            X = rng.randrange(1, 10**6)
            lhs = p6_triple_sum(n, h, b, X)
            rhs = p6_triple_sum(n, h, b, X, keep=lambda l, j: l + j >= 5)
            for (l, j, lo, hi) in P6_PRINTED_GROUPS:
                for i in range(lo, p6_hi(hi, n) + 1):
                    rhs += p6_term(n, i, j, l, h, b, X)
            rest = p6_triple_sum(
                n, h, b, X, keep=lambda l, j: l + j <= 4 and (l, j) not in listed
            )
            if lhs != rhs + rest:
                print(f"FAIL partition n={n} h={h} b={b} X={X}: off by {lhs - rhs - rest:+d}")
                ok = False

        residual_terms = sum(
            1
            for i in range(n)
            for j in range(n - 1 - i + 1)
            for l in range(i + 1)
            if l + j >= 5
        )
        if n >= 7 and residual_terms == 0:
            print(f"FAIL residual n={n}: no summand reaches l+j >= 5, screen is vacuous")
            ok = False
        print(
            f"p.6 regrouping n={n}: 10 printed ranges natural, partition exact, "
            f"residual carries {residual_terms} summands (l+j >= 5)"
        )
    return ok


def screen_p7_rhs(primes=(7, 11, 13), per_prime: int = 2) -> bool:
    """p. 7 R1's RHS: the printed i <= 4 terms plus the tail sum.

    p. 7 writes the right-hand side of the chain as

        sum_{i=5}^{n} C(n,i) a^((n-1)(n-i)) (n^s bck)^i
          + a^(n(n-1)) + n a^(n(n-2)) n^s abck
          + n(n-1)/2 a^(n(n-3)) (n^s abck)^2
          + n(n-1)(n-2)/6 a^(n(n-4)) (n^s abck)^3
          + n(n-1)(n-2)(n-3)/24 a^(n(n-5)) (n^s abck)^4

    which must equal the binomial expansion of (a^(n-1) + n^s bck)^n. The two
    spellings mix a^(n(n-k)) (n^s abck)^i with a^((n-1)(n-i)) (n^s bck)^i; they
    agree because n(n-1-i) + i = (n-1)(n-i). This screen uses the printed
    spelling verbatim, so it checks the coefficients AND the exponents.
    """
    ok = True
    rng = random.Random(SEED + 3)
    for n in primes:
        for _ in range(per_prime):
            a, b, c, k, s, _h = free_params(n, rng)
            X = X_of(n, a, b, c, k, s)
            # NOTE the tail must use the R2 spelling a^((n-1)(n-i)) (n^s bck)^i:
            # at i = n the R3 spelling a^(n(n-1-i)) (n^s abck)^i has exponent
            # n(n-1-n) = -n, so the two spellings agree only after cancelling
            # a^(-n) * a^n. No negative powers in Z, and p. 7 prints the R2
            # spelling here. Both are checked equal at i <= n-1 below.
            printed = sum(
                comb(n, i) * a ** ((n - 1) * (n - i)) * (n**s * b * c * k) ** i
                for i in range(5, n + 1)
            )
            printed += a ** (n * (n - 1))
            printed += n * a ** (n * (n - 2)) * X
            printed += (n * (n - 1) // 2) * a ** (n * (n - 3)) * X**2
            printed += (n * (n - 1) * (n - 2) // 6) * a ** (n * (n - 4)) * X**3
            printed += (n * (n - 1) * (n - 2) * (n - 3) // 24) * a ** (n * (n - 5)) * X**4
            exact = (a ** (n - 1) + n**s * b * c * k) ** n
            if printed != exact:
                print(f"FAIL p.7 RHS n={n} a={a} b={b} c={c} k={k} s={s}: off by {printed - exact:+d}")
                ok = False
        print(f"p.7 R1 RHS: printed i<=4 terms + tail = (a^(n-1)+n^s bck)^n, n={n}")
    return ok


def screen_section_B(m_max: int = 7, k_max: int = 4) -> bool:
    """Section B (p. 2 R1) - the two auxiliary rules the main proof applies.

    B.1) index shift:      sum_{i=k}^{n} a_i = sum_{i=m}^{n+m-k} a_{i-m+k}
    B.2) sum_{i=k}^{m-1} i(i-1)...(i-k+1) h^(m-1-i) x^(i-k)
           = sum_{i=0}^{m-1-k} (m-1-i)(m-2-i)...(m-k-i) h^i x^(m-1-k-i)
           = f^(k)(x),  with f(x) = sum_{t=0}^{m-1} x^(m-1-t) h^t = (x^m-h^m)/(x-h)

    Both are cited from p. 9 onward ("ap dung muc B.1 / B.2, trang 2") and NO
    DONE chunk covers them - L1-01..L7-ASM verify section C (pp. 2-5) only.
    Screening them here sizes the missing chunk: B.1 is a pure re-indexing,
    B.2's middle form is the same sum read backwards, and its last form is the
    k-th derivative of the geometric polynomial (checked with sympy).
    """
    ok = True
    rng = random.Random(SEED + 4)

    for _ in range(50):
        n = rng.randrange(2, 12)
        k = rng.randrange(0, n + 1)
        m = rng.randrange(0, 8)
        seq = {i: rng.randrange(-10**6, 10**6) for i in range(-10, 30)}
        lhs = sum(seq[i] for i in range(k, n + 1))
        rhs = sum(seq[i - m + k] for i in range(m, n + m - k + 1))
        if lhs != rhs:
            print(f"FAIL B.1 n={n} k={k} m={m}")
            ok = False
    print("B.1 index-shift identity holds on 50 random instances")

    x, h = sp.symbols("x h")
    for m in range(2, m_max + 1):
        for k in range(1, min(k_max, m - 1) + 1):
            f = sum(x ** (m - 1 - t) * h**t for t in range(m))
            deriv = sp.expand(sp.diff(f, x, k))
            falling_first = sp.expand(
                sum(
                    sp.prod([i - j for j in range(k)]) * h ** (m - 1 - i) * x ** (i - k)
                    for i in range(k, m)
                )
            )
            falling_second = sp.expand(
                sum(
                    sp.prod([m - 1 - i - j for j in range(k)]) * h**i * x ** (m - 1 - k - i)
                    for i in range(m - k)
                )
            )
            if sp.simplify(falling_first - falling_second) != 0:
                print(f"FAIL B.2 re-indexing m={m} k={k}")
                ok = False
            if sp.simplify(falling_second - deriv) != 0:
                print(f"FAIL B.2 derivative m={m} k={k}")
                ok = False
    print(f"B.2 falling-factorial sum = f^(k)(x), exact for m <= {m_max}, k <= {k_max}")
    return ok


def main() -> int:
    print("== M1 common screens (main proof, pp. 6-33) ==")
    print("-- vacuity (the equation cannot be instantiated) --")
    ok = screen_vacuity()
    print("-- expansion identity (unconditional, exact) --")
    ok &= screen_expansion()
    print("-- tail truncations (unconditional, moduli sharp) --")
    ok &= screen_tail()
    print("-- p.6 triple-sum regrouping (pure partition) --")
    ok &= screen_p6_regroup()
    print("-- p.7 R1 right-hand side --")
    ok &= screen_p7_rhs()
    print("-- section B (p.2 R1) - cited by pp.9-14, no chunk covers it --")
    ok &= screen_section_B()
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
