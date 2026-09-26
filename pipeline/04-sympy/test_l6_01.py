"""Stage 4 smoke for chunk L6-01 (bo de 6).

Lemma 6 (statement p. 1, section A; proof p. 3 sec. 6 - p. 4):
n is an odd prime. Suppose the Fermat equation

    x^n + y^n = z^n   (1)

has a nonzero integer solution x = u, y = v, z = t with
(u,v) = (u,t) = (v,t) = 1 and uv NOT divisible by n. Then there exist
nonzero a, b, c, k, pairwise coprime and none of them divisible by n, and
an integer s > 1, such that

    v = a^n + n^s abck,   u = b^n + n^s abck,
    t = h - n^s abck,     a^n + b^n = h - 2 n^s abck,
    h = c^n  if n does not divide t,
    h = n^(ns-1) c^n  if n divides t.

VACUITY OF THE HYPOTHESES -- the central caveat of this screen.
n is an odd prime, hence n >= 3, so by Fermat's Last Theorem equation (1)
has NO nonzero integer solution. The boxed search below (n in {5,7,11,13},
|u|,|v| <= 24) finds 0 candidates: an instance-based witness search for
lemma 6 is impossible, and nothing in this file is evidence FOR the lemma.
Everything the proof does is conditional on an unsatisfiable hypothesis.
What is screened here is the INFERENCE content, in three parts:

  (A) the unconditional identities / congruences the proof uses, each on a
      numeric box (n in {5,7,11,13} throughout):
      - the three factorisations (3) => (4),(5),(6)  [S2];
      - n | (u+v) => n | u^n + v^n, n | (t-v) => n | t^n - v^n,
        n | (t-u) => n | t^n - u^n, and (n prime) n | x^n => n | x,
        which together give the 6.1 branch's "(u+v), (t-v), (t-u) not
        divisible by n"  [S3, S4];
      - n prime: C(n,k) = 0 mod n (1 <= k <= n-1) and
        x^(n-1) = 1 mod n, x^n = x mod n  (little Fermat)  [S7, S8];
      - the printed c'^n - 1 decomposition identity, and its consequence
        c'^n - 1 = 0 mod n  [S7, S8];
      - n prime, n does not divide c': c'^n = 1 mod n  =>  c' = 1 mod n,
        i.e. c' = 1 + n k_3  [S9];
      - (1 + n k)^n - 1 = 0 mod n^2, and 2 X = 0 mod n^2 => X = 0 mod n^2
        for n odd  [S11, S12];
      - the 6.2 algebra (4'')/(5'')  [S15, S16, S17];
      - the 6.2.1 k = 0 contradiction  [S25, S26];
      - the u+v-t = n^s abck shape and the s >= 2 claim  [S13, S23].

  (B) the CONCLUSION's parametrisation, on a constructed family where it is
      honestly checkable: with X = n^s abck and h the printed alternative,
      the four printed formulas reproduce u+v = h, t = h - X,
      t - v = b^n, t - u = a^n, u+v-t = X and n^2 | X -- i.e. they are
      exactly the printed (4'),(5'),(6') resp. (4'') plus the n^s abck
      relation of S13/S23. They do NOT reproduce u^n + v^n = t^n
      (machine-checked below): that is (1) itself, unsatisfiable for
      n >= 3. So the paper's modular hypotheses stay load-bearing for the
      step (1) => conclusion; the shape check certifies only that the
      printed conclusion is consistent with the printed intermediate
      formulas and with BOTH printed h-alternatives.

  (C) RED FLAGS -- hypotheses shown load-bearing by exhibiting the failure
      once dropped:
      - n primality: for composite n the steps "C(n,k) = 0 mod n" and
        "x^(n-1) = 1 mod n" fail, and c'^n = 1 mod n does NOT give
        c' = 1 mod n (n = 4, c' = 3);
      - n odd: for n = 2 the step 2 X = 0 mod n^2 => X = 0 mod n^2 fails;
      - "a, b, c not divisible by n" (the 6.2/6.1 reading of the notation
        (a,b) = (a,c) = (c,b) = 1 plus uv not divisible by n): dropping it
        lets s = 1 while n^2 | u+v-t, so the printed s >= 2 fails;
      - "uv not divisible by n": dropping it allows n | a, which makes
        t - u = a^n divisible by n and kills the "(t-u) not divisible by
        n" fact the proof derives in BOTH branches (p. 4, 6.1 and 6.2).

Exit 0 = "no transcription red flag on the searched range"; this is a smoke
screen, not a proof.
"""

import math
import sys

import sympy

N_SET = (5, 7, 11, 13)


def v_p(x, p):
    """p-adic valuation of a nonzero integer (p prime)."""
    assert x != 0, "v_p of 0"
    k = 0
    x = abs(x)
    while x % p == 0:
        x //= p
        k += 1
    return k


def A_sum(u, v, n):
    """The alternating sum of (4): sum_{i=0}^{n-1} (-1)^i u^{n-1-i} v^i."""
    return sum((-1) ** i * u ** (n - 1 - i) * v ** i for i in range(n))


def B_sum(x, y, n):
    """The plain sum of (5)/(6): sum_{i=0}^{n-1} x^{n-1-i} y^i."""
    return sum(x ** (n - 1 - i) * y ** i for i in range(n))


def signed_iroot(p_, n):
    """Exact integer n-th root of p_, or None (odd n: sign carried)."""
    if n % 2 == 0:
        if p_ < 0:
            return None
        r, exact = sympy.integer_nthroot(p_, n)
        return int(r) if exact else None
    neg = p_ < 0
    r, exact = sympy.integer_nthroot(abs(p_), n)
    if not exact:
        return None
    return -int(r) if neg else int(r)


def check_vacuity(limit=24, n_set=N_SET):
    """The hypotheses of lemma 6 are unsatisfiable: no nonzero solution of
    x^n + y^n = z^n exists for n >= 3 (FLT), so no witness-based screen of
    the lemma is possible. Also verifies the neighbouring non-vacuous
    cases n = 1, 2, used below as the only real instances of (3)."""
    cand = 0
    for n in n_set:
        for u in range(-limit, limit + 1):
          for v in range(-limit, limit + 1):
            if u == 0 or v == 0:
                continue
            t = signed_iroot(u ** n + v ** n, n)
            if t is None or t == 0:
                continue
            cand += 1
            print(f"VACUITY FAIL: witness n={n} u={u} v={v} t={t}")
    assert cand == 0, "vacuity: unexpected FLT witness in the box"
    print(f"vacuity ok (n in {n_set}, |u|,|v| <= {limit}: 0 solutions of (1)"
          f" -- the hypothesis of bo de 6 is unsatisfiable; all steps below"
          f" are screened as inferences, not on witnesses)")
    # the only honest instances of (3): n = 1 and n = 2 (u^n + v^n = z^n
    # has solutions there). Note (4) is the ODD-n factorisation of a SUM
    # (n = 2 would give u^2 + v^2 = (u+v)(u-v), false), while (5),(6) are
    # the difference factorisations and hold for every n.
    for (u, v, t, n) in ((2, 3, 5, 1), (7, -4, 3, 1)):
        assert u ** n + v ** n == t ** n, "small-n instance of (3)"
        assert (u + v) * A_sum(u, v, n) == t ** n, "small-n (4) (n odd)"
        assert (t - v) * B_sum(t, v, n) == u ** n, "small-n (5)"
        assert (t - u) * B_sum(t, u, n) == v ** n, "small-n (6)"
    u, v, t, n = 3, 4, 5, 2
    assert u ** n + v ** n == t ** n, "small-n instance of (3) at n = 2"
    assert (t - v) * B_sum(t, v, n) == u ** n, "small-n (5) at n = 2"
    assert (t - u) * B_sum(t, u, n) == v ** n, "small-n (6) at n = 2"
    assert (u + v) * A_sum(u, v, n) == u ** n - v ** n, \
        "at even n the alternating sum factors the DIFFERENCE, not the sum (n odd is load-bearing for (4))"
    print("small-n ok (n=1: (2,3,5) and (7,-4,3): (3) => (4),(5),(6); n=2: (3,4,5): "
          "(5),(6) only -- (4) is the odd-n factorisation of a SUM, so 'n nguyen to le' "
          "is load-bearing for it)")
    return True


def check_factorisations(low=-6, high=6, n_set=N_SET):
    """S1+S2: u^n + v^n = (u+v) * sum (-1)^i u^{n-1-i} v^i  (identity), and
    t^n - v^n = (t-v) * sum t^{n-1-i} v^i,  t^n - u^n = (t-u) * sum t^{n-1-i} u^i.
    Under (3) (t^n - v^n = u^n, t^n - u^n = v^n) these are (4), (5), (6)."""
    cnt = 0
    for n in n_set:
        for u in range(low, high + 1):
            for v in range(low, high + 1):
                assert (u + v) * A_sum(u, v, n) == u ** n + v ** n, "S2: (4)"
                for t in (low, -1, 0, 1, high):
                    assert (t - v) * B_sum(t, v, n) == t ** n - v ** n, "S2: (5)"
                    assert (t - u) * B_sum(t, u, n) == t ** n - u ** n, "S2: (6)"
                cnt += 1
    print(f"factorisations ok ({cnt} (u,v) pairs, n in {n_set}: (3) => (4),(5),(6) "
          f"reduce to these unconditional identities)")
    return True


def check_61_head(low=-8, high=8, n_set=N_SET):
    """S3+S4 (6.1 head): with (4),(5),(6) and n prime,
      n | (u+v)  => n | u^n + v^n = t^n   => n | t,
      n | (t-v)  => n | t^n - v^n = u^n   => n | u,
      n | (t-u)  => n | t^n - u^n = v^n   => n | v.
    So the 6.1 hypothesis (t NOT divisible by n) rules out n | (u+v), and
    uv NOT divisible by n (with n prime, so n does not divide u or v)
    rules out n | (t-v) and n | (t-u). Both halves are unconditional facts
    about integers, checked here over a box; the composition uses (3)."""
    cnt = 0
    for n in n_set:
        assert sympy.isprime(n), "n prime"
        for x in range(low, high + 1):
            # (n prime) n | x^n <=> n | x
            assert ((x ** n) % n == 0) == (x % n == 0), "n prime: n | x^n <=> n | x"
        for u in range(low, high + 1):
            for v in range(low, high + 1):
                for t in range(low, high + 1):
                    if (u + v) % n == 0:
                        assert (u ** n + v ** n) % n == 0, "S3: n | (u+v) => n | (u+v)A"
                    if (t - v) % n == 0:
                        assert (t ** n - v ** n) % n == 0, "S4: n | (t-v) => n | (t-v)B"
                    if (t - u) % n == 0:
                        assert (t ** n - u ** n) % n == 0, "S4: n | (t-u) => n | (t-u)C"
                    cnt += 1
    print(f"6.1 head ok ({cnt} triples, n in {n_set}: n | (u+v),(t-v),(t-u) forces "
          f"n | t,u,v resp.; the case hypothesis t not-divisible-by-n and uv "
          f"not-divisible-by-n then contradict it)")
    return True


def check_61_flt(low=-20, high=20, n_set=N_SET):
    """S7+S8 (p. 3 tail - p. 4 head): n prime gives C(n,k) = 0 mod n for
    1 <= k <= n-1 (needed since (u+v) is a factor of every term), and
    little Fermat (u+v)^(n-1) = 1 mod n when n does not divide (u+v),
    so [(u+v)^(n-1) - 1] = 0 mod n. Both are used to get c'^n - 1 = 0 mod n."""
    for n in n_set:
        for k in range(1, n):
            assert math.comb(n, k) % n == 0, f"S8: C({n},{k}) = 0 mod n"
        for x in range(low, high + 1):
            if x % n == 0:
                continue
            assert (x ** (n - 1) - 1) % n == 0, "S9: FLT mod n"
            assert (x ** n - x) % n == 0, "S9: x^n = x mod n"
    print(f"FLT mod n ok (n in {n_set}: C(n,k) = 0 mod n for 1 <= k <= n-1, "
          f"(u+v)^(n-1) = 1 mod n for n not dividing (u+v))")
    return True


def check_61_cprime_identity(low=-5, high=5, n_set=N_SET):
    """S7+S8: with A = sum (-1)^i u^{n-1-i} v^i = c'^n (from (4'), bo de 3),
      c'^n - 1 = sum_{k=1}^{n-1} (-1)^k C(n,k) (u+v)^{n-k-1} v^k + [(u+v)^{n-1} - 1]
    is an identity (the k=0 term of A is exactly (u+v)^{n-1}), and for
    n prime with n not dividing (u+v) every term on the right is divisible
    by n, so c'^n - 1 = 0 mod n."""
    cnt = 0
    for n in n_set:
        for u in range(low, high + 1):
            for v in range(low, high + 1):
                A = A_sum(u, v, n)
                assert A == sum((-1) ** k * math.comb(n, k) * (u + v) ** (n - 1 - k) * v ** k
                                for k in range(n)), "A = sum C(n,k)(u+v)^{n-1-k}v^k"
                rhs = (sum((-1) ** k * math.comb(n, k) * (u + v) ** (n - k - 1) * v ** k
                           for k in range(1, n))
                       + ((u + v) ** (n - 1) - 1))
                assert A - 1 == rhs, "S8: the c'^n - 1 decomposition identity"
                if (u + v) % n != 0:
                    assert (A - 1) % n == 0, "S9: c'^n - 1 = 0 mod n"
                cnt += 1
    print(f"c'^n - 1 identity ok ({cnt} (u,v) pairs, n in {n_set}: the printed "
          f"decomposition is an identity and gives c'^n - 1 = 0 mod n for "
          f"n prime, n not dividing u+v)")
    return True


def check_61_cprime_congruence(low=-30, high=30, n_set=N_SET):
    """S9+S10: n prime, n not dividing c'; from c'^n - 1 = 0 mod n (c'^n = c'
    mod n) the proof gets c'^(n-1) - 1 = 0 mod n, then
    c'^n - 1 - (c'^(n-1) - 1) = c'^(n-1)(c' - 1) = 0 mod n, hence n | c' - 1,
    i.e. c' = 1 + n k_3; the same for a' = 1 + n k_1, b' = 1 + n k_2."""
    cnt = 0
    for n in n_set:
        for c in range(low, high + 1):
            if c == 0 or c % n == 0:
                continue
            # FLT halves, unconditional for n prime:
            assert (c ** (n - 1) - 1) % n == 0, "S10: FLT gives c'^(n-1) - 1 = 0 mod n"
            assert (c ** n - c) % n == 0, "S10: c'^n - c' = 0 mod n"
            # the printed case hypothesis "c'^n - 1 = 0 mod n" (which the
            # identity + FLT of S8 supplies as c' - 1 = 0 mod n):
            assert (c ** n - 1) % n == (c - 1) % n, "S10: c'^n - 1 = c' - 1 mod n"
            if (c ** n - 1) % n == 0:
                assert (c ** (n - 1) - 1) % n == 0, "S10: (c'^(n-1)-1) = 0 mod n"
                assert (c ** (n - 1) * (c - 1)) % n == 0, "S10: c'^(n-1)(c'-1) = 0 mod n"
                assert (c * (c - 1)) % n == 0, "S10: c'(c'-1) = 0 mod n (printed)"
                assert (c - 1) % n == 0, "S10: c' = 1 mod n"
                cnt += 1
    print(f"c' = 1 + n k_3 ok ({cnt} residues with c'^n = 1 mod n, n in {n_set}: "
          f"n prime and n not dividing c' turn c'^n - 1 = 0 mod n into c' = 1 mod n; "
          f"note the printed intermediate 'c'^(n-1) - 1 = 0 mod n' is FLT and holds "
          f"unconditionally, while c'^n - 1 = 0 mod n is the real case hypothesis)")
    return True


def check_61_nsquare(low=-40, high=40, k_max=4, n_set=N_SET):
    """S11+S12: b'^n = (1 + n k_2)^n makes
    u^n - t + v = b^n[(1+n k_2)^n - 1] = 0 mod n^2 (same for a'), so
    (u^n-t+v) + (v^n-t+u) - (t^n-u-v) = 2(u+v-t) = 0 mod n^2, and n odd
    (2 invertible mod n^2) gives (u+v-t) = 0 mod n^2."""
    for n in n_set:
        for k in range(-k_max, k_max + 1):
            assert ((1 + n * k) ** n - 1) % (n * n) == 0, "S11: (1+nk)^n - 1 = 0 mod n^2"
        for X in range(low, high + 1):
            if (2 * X) % (n * n) == 0:
                assert X % (n * n) == 0, "S12: 2X = 0 mod n^2 => X = 0 mod n^2"
        for a in range(1, 4):
            for k in range(-2, 3):
                for c in (-3, -2, 2, 3):
                    v = c ** n * ((1 + n * k) ** n - 1)
                    assert v % (n * n) == 0, "S12: c^n[(1+nk_3)^n-1] = 0 mod n^2"
                    v = a ** n * ((1 + n * k) ** n - 1)
                    assert v % (n * n) == 0, "S24: a^n[(1+nk_1)^n-1] = 0 mod n^2"
                    v = a ** n * ((1 + n * k) ** n - 1)
                    assert v % (n * n) == 0, "S24: b^n[(1+nk_2)^n-1] = 0 mod n^2"
    for u, v, t in ((2, 3, 5), (7, -4, 1), (-6, 11, 2)):
        lhs = (u ** 5 - t + v) + (v ** 5 - t + u) - (t ** 5 - u - v)
        assert lhs == (u ** 5 + v ** 5 - t ** 5) + 2 * (u + v - t), "S14: sum identity"
    print(f"n^2 chain ok (n in {n_set}: (1+nk)^n - 1, c^n[(1+nk)^n-1], "
          f"a^n[...], b^n[...] all 0 mod n^2; 2X = 0 mod n^2 => X = 0 mod n^2 "
          f"for n odd; the three-term sum identity = (u^n+v^n-t^n) + 2(u+v-t))")
    return True


def check_param_shape(n_set=N_SET):
    """S13+S23: the shape u+v-t = n^s abck. Constructed families with
    a,b,c,k pairwise coprime and n not dividing abck: then n^2 | u+v-t and
    s = v_n(u+v-t) >= 2 exactly; and conversely -- given n^2 | u+v-t,
    n not dividing abc and k nonzero with n not dividing k -- the printed
    representation forces s >= 2."""
    cnt = 0
    for n in n_set:
        for s in (2, 3, 4):
            for a, b, c, k in ((1, 1, 1, 1), (2, 3, 5, 7), (-1, 2, 3, -2),
                               (4, 9, 25, 3)):
                if math.gcd(abs(a), abs(b)) != 1 or math.gcd(abs(a), abs(c)) != 1 \
                        or math.gcd(abs(c), abs(b)) != 1 or a % n == 0 or b % n == 0 \
                        or c % n == 0 or k % n == 0 or k == 0:
                    continue
                X = n ** s * a * b * c * k
                assert X % (n * n) == 0, "S13: n^2 | n^s abck for s >= 2"
                assert v_p(X, n) == s, "S13: v_n(n^s abck) = s when n does not divide abck"
                cnt += 1
        # converse used by the printed "nen s >= 2"
        for s in (1, 2, 3):
            for a, b, c, k in ((1, 1, 1, 1), (2, 3, 5, 7), (3, 5, 7, 11)):
                if a % n == 0 or b % n == 0 or c % n == 0 or k % n == 0:
                    continue
                X = n ** s * a * b * c * k
                if X % (n * n) == 0:
                    assert s >= 2, "S13: n^2 | n^s abck with n not dividing abck => s >= 2"
    print(f"parametrisation shape ok ({cnt} constructed (n,s,a,b,c,k): "
          f"u+v-t = n^s abck with n not dividing abck gives n^2 | u+v-t and "
          f"s = v_n(u+v-t) >= 2, and conversely)")
    return True


def check_62_algebra(n_set=N_SET):
    """S15-S17 (6.2): the printed (4'') and (5''). With t = n^s c c' and
    u+v = n^(sn-1) c^n as printed in (4''),
      t^n - u - v = (n^s c c')^n - n^(sn-1) c^n = n^(sn-1) c^n [n c'^n - 1]  (5''),
    which is 0 mod n^2 as soon as s >= 1 and n >= 3. The printed exponent
    of (4'')/(5'') is "sn-1" while the next line and the statement print
    "ns-1" (chunk L6-01 red flag, see p004.yml notes): the identity holds
    with either letter order because s*n - 1 = n*s - 1."""
    cnt = 0
    for n in n_set:
        for s in (1, 2, 3):
            for c, cp in ((1, 1), (-2, 3), (5, -7), (4, 9)):
                if c % n == 0 or cp % n == 0:
                    continue
                t = n ** s * c * cp
                uvp = n ** (s * n - 1) * c ** n          # (4'') as printed: n^{sn-1}c^n
                assert t ** n - uvp == n ** (s * n - 1) * c ** n * (n * cp ** n - 1), \
                    "S17: (5'') as printed"
                assert (t ** n - uvp) % (n * n) == 0, "S17: t^n - u - v = 0 mod n^2"
                assert n ** (s * n - 1) == n ** (n * s - 1), "red flag: sn-1 = ns-1"
                uvp2 = n ** (n * s - 1) * c ** n         # the ns-1 reading of the same line
                assert t ** n - uvp2 == n ** (n * s - 1) * c ** n * (n * cp ** n - 1), \
                    "S17: (5'') with the ns-1 letter order"
                # (4'')/summary consistency: h = n^{ns-1}c^n = u+v
                assert uvp2 == uvp, "red flag: n^{sn-1}c^n = n^{ns-1}c^n"
                cnt += 1
        # s >= 1 and n odd prime >= 3 give v_n(n^{sn-1}) >= 2
        for s in (1, 2):
            tot = s * n - 1
            assert tot >= 2, "S17: v_n(n^{sn-1}c^n) = sn-1 >= 2"
    print(f"6.2 (4'')/(5'') ok ({cnt} instances, n in {n_set}: the printed (5'') "
          f"identity holds and gives n^2 | t^n-u-v; the printed exponent order "
          f"sn-1 vs ns-1 is typographic -- n^(sn-1) = n^(ns-1))")
    return True


def check_621_k0(n_set=N_SET):
    """S25+S26 (6.2.1, k = 0): then u+v = t, so t-u = v and t-v = u; with
    (6') t-u = a^n and v = a a' this gives a^n = a a', i.e. a^(n-1) = a',
    and (a,a') = 1 forces |a| = |a'| = 1 (same for b). Hence u = b^n, v = a^n
    are +-1, t = u+v in {-2,0,2}, and t^n = u^n + v^n = u + v = t (n odd):
    t = 0 (impossible in a nonzero solution) or t^n = +-2 (impossible for
    n >= 2)."""
    cnt = 0
    for n in n_set:
        for a in (1, -1):
            for b in (1, -1):
                ap = a ** (n - 1)                     # a' = a^(n-1)
                bp = b ** (n - 1)
                assert math.gcd(abs(a), abs(ap)) == 1, "S25: (a,a') = 1 with |a| = 1"
                assert math.gcd(abs(b), abs(bp)) == 1, "S25: (b,b') = 1 with |b| = 1"
                assert abs(a) == abs(ap) == abs(b) == abs(bp) == 1, "S25: |a|=|a'|=|b|=|b'|=1"
                u, v, t = b ** n, a ** n, a ** n + b ** n
                assert u ** n == u and v ** n == v, \
                    "S25/S26: odd n and |a| = |b| = 1 give u^n = u, v^n = v"
                assert u ** n + v ** n == u + v == t, "S26: u^n + v^n = u+v = t"
                assert t == u + v and t in (-2, 0, 2), "S25: t = u+v in {-2,0,2}"
                if t == 0:
                    assert u ** n + v ** n == 0, "S26: t = 0 branch (mixed signs)"
                else:
                    # (3) would give t^n = u^n + v^n = t, i.e. the printed
                    # "t^n = 2" (u = v = 1) resp. "t^n = -2" (u = v = -1);
                    # impossible for |t| = 2 and n >= 3
                    assert u ** n + v ** n in (2, -2), "S26: printed alternative t^n = +-2"
                    assert t ** (n - 1) != 1 and t ** n != t, \
                        "S26: t^n = t (t^n = +-2) is impossible for |t| = 2 and n >= 3"
                cnt += 1
    # the printed alternative "t = 0 or t^n = 2": the positive-sign branch
    # a = b = 1 gives t^n = 1 + 1 = 2, the negative one a = b = -1 gives
    # t^n = -1 - 1 = -2; both are absurd for n >= 2.
    n = 5
    assert 1 ** n + 1 ** n == 2 and (-1) ** n + (-1) ** n == -2, \
        "S26: sign branches give t^n = 2 resp. t^n = -2"
    print(f"6.2.1 (k = 0) ok ({cnt} sign patterns, n in {n_set}: |a|=|a'|=|b|=|b'|=1, "
          f"t = u+v in {{-2,0,2}}, and t^n = u^n+v^n forces t = 0 or t^n = +-2; "
          f"printed 't^n = 2' is the positive-sign branch, the negative one gives "
          f"t^n = -2, both absurd for n >= 2)")
    return True


def check_conclusion_shape(n_set=N_SET, search_max=8):
    """(B) The conclusion's parametrisation, where it is honestly checkable.

    X = n^s abck and h the printed alternative (h = c^n for 6.1, h = n^(ns-1)c^n
    for 6.2); the four printed formulas are
        v = a^n + X, u = b^n + X, t = h - X, a^n + b^n = h - 2X.
    (i)   symbolic: the printed relation a^n + b^n = h - 2X plus the four
          formulas imply t = h - X, u + v = h, t - v = b^n, t - u = a^n,
          u + v - t = X = n^s abck -- exactly the printed (4')/(4'') and
          (5')/(6') plus the u+v-t relation of S13/S23, and this does not
          depend on WHICH h-alternative is meant.
    (ii)  numeric: the same relations on concrete families (n in {5,7,11,13},
          s >= 2, pairwise coprime a,b,c,k not divisible by n), n^2 | u+v-t.
    (iii) a bounded search for FULLY coupled instances -- the h alternative
          satisfied exactly and k integral, i.e. 2 n^s abc | h - a^n - b^n,
          plus the lemma's side conditions on a,b,c,k,s. With the printed
          pairwise coprimality of k enforced the box is empty (reported as
          UNDETERMINED, not as a red flag); with that one clause relaxed
          instances exist, each satisfying every other printed relation and
          FAILING u^n + v^n = t^n. So the printed shape does not force (1):
          (1)/(3) stays an independent hypothesis.
    (iv)  the relaxed instances' (u,v,t) also satisfy (u,v) = (u,t) = (v,t) = 1
          and uv not divisible by n (reported per instance): the conclusion's
          own numbers are consistent with the lemma's hypotheses on u, v, t;
          only (1)/(3) cannot hold."""
    # (i) symbolic relations, valid for both h-alternatives
    a, b, c, k, n, s = sympy.symbols("a b c k n s", positive=True)
    X = n ** s * a * b * c * k
    h = a ** n + b ** n + 2 * X            # the printed "a^n + b^n = h - 2X"
    u, v, t = b ** n + X, a ** n + X, h - X
    assert sympy.simplify(t - (h - X)) == 0, "shape: t = h - X"
    assert sympy.simplify((u + v) - h) == 0, "shape: u+v = h"
    assert sympy.simplify((t - v) - b ** n) == 0, "shape: t-v = b^n"
    assert sympy.simplify((t - u) - a ** n) == 0, "shape: t-u = a^n"
    assert sympy.simplify((u + v - t) - X) == 0, "shape: u+v-t = X = n^s abck"
    assert sympy.simplify((u - b ** n) - X) == 0 and sympy.simplify((v - a ** n) - X) == 0, \
        "shape: u-b^n = v-a^n = X"
    # (ii) numeric families (h defined by the printed relation, as in (i))
    cnt = 0
    for n in n_set:
        for s in (2, 3):
            for a, b, c, k in ((1, 1, 1, 1), (2, 3, 5, 7), (4, 9, 25, 3),
                               (-1, 2, 3, -2)):
                if a % n == 0 or b % n == 0 or c % n == 0 or k % n == 0:
                    continue
                X = n ** s * a * b * c * k
                h = a ** n + b ** n + 2 * X
                u, v, t = b ** n + X, a ** n + X, h - X
                assert t == h - X and u + v == h, f"shape n={n}: t = h-X, u+v = h"
                assert u + v - t == X == n ** s * a * b * c * k, f"shape n={n}: u+v-t"
                assert X % (n * n) == 0, f"shape n={n}: n^2 | u+v-t (s >= 2)"
                assert t - v == b ** n and t - u == a ** n, f"shape n={n}: (5'),(6')"
                assert u - b ** n == X and v - a ** n == X, f"shape n={n}: kernels"
                cnt += 1
    # (iii)+(iv) fully coupled instances: h alternative satisfied exactly,
    # k integral (2 n^s abc | h - a^n - b^n), all the lemma's side conditions
    # except (1) itself. "relaxed" drops only the pairwise coprimality of k.
    strict, relaxed = [], []
    for n in (3, 5):
        for s in (2, 3):
            for a in range(1, search_max + 1):
                for b in range(1, search_max + 1):
                    for c in range(1, search_max + 1):
                        if any(x % n == 0 for x in (a, b, c)):
                            continue
                        if math.gcd(a, b) != 1 or math.gcd(a, c) != 1 or math.gcd(b, c) != 1:
                            continue
                        for h, branch in ((c ** n, "6.1"), (n ** (n * s - 1) * c ** n, "6.2")):
                            den = 2 * n ** s * a * b * c
                            num = h - a ** n - b ** n
                            if num % den:
                                continue
                            kk = num // den
                            if kk == 0 or kk % n == 0:
                                continue
                            X = n ** s * a * b * c * kk
                            if X % (n * n):
                                continue
                            uu, vv, tt = b ** n + X, a ** n + X, h - X
                            if 0 in (uu, vv, tt):
                                continue
                            # the printed formulas, verbatim
                            assert uu + vv == h, f"coupled {branch}: u+v = h"
                            assert a ** n + b ** n == h - 2 * X, f"coupled {branch}: a^n+b^n"
                            assert uu - b ** n == X and vv - a ** n == X, f"coupled {branch}: kernels"
                            assert tt - vv == b ** n and tt - uu == a ** n, \
                                f"coupled {branch}: (5'),(6')"
                            assert uu + vv - tt == X == n ** s * a * b * c * kk, \
                                f"coupled {branch}: u+v-t = n^s abck"
                            assert X % (n * n) == 0, f"coupled {branch}: n^2 | u+v-t"
                            assert s >= 2, f"coupled {branch}: s >= 2"
                            # it is NOT a solution of (1) (FLT)
                            assert uu ** n + vv ** n != tt ** n, \
                                f"coupled {branch}: (1) must fail (FLT)"
                            rec = (branch, n, s, a, b, c, kk, (uu, vv, tt),
                                   (math.gcd(abs(uu), abs(vv)) == 1
                                    and math.gcd(abs(uu), abs(tt)) == 1
                                    and math.gcd(abs(vv), abs(tt)) == 1),
                                   (uu * vv) % n != 0)
                            relaxed.append(rec)
                            if all(math.gcd(abs(kk), x) == 1 for x in (a, b, c)):
                                strict.append(rec)
    n61 = [f for f in strict if f[0] == "6.1"]
    n62 = [f for f in strict if f[0] == "6.2"]
    print(f"conclusion shape ok (symbolic: the four printed formulas imply "
          f"t = h-X, u+v = h, t-v = b^n, t-u = a^n, u+v-t = n^s abck, for either "
          f"h-alternative; numeric: {cnt} families, n in {n_set}, s >= 2, pairwise "
          f"coprime a,b,c,k not divisible by n, n^2 | u+v-t)")
    print(f"  coupled instances (h exact, k integral, n in (3,5), s in (2,3), "
          f"a,b,c <= {search_max}): with the conclusion's pairwise coprimality of "
          f"k enforced -- 6.1 {len(n61)}, 6.2 {len(n62)}; UNDETERMINED: the "
          f"conclusion's satisfiability is not established by this search, and an "
          f"empty box is not evidence either way. With coprimality of k RELAXED "
          f"{len(relaxed)} instance(s) exist, each satisfying every printed "
          f"relation (u+v = h, t-v = b^n, t-u = a^n, u+v-t = n^s abck, n^2 | u+v-t, "
          f"a,b,c pairwise coprime, n not dividing abck) while FAILING k pairwise "
          f"coprime and FAILING u^n+v^n = t^n: {relaxed[:2]} (tuple = branch, n, s, "
          f"a, b, c, k, (u,v,t), coprime-triple-of-u,v,t, uv not divisible by n) -- "
          f"so the printed shape does NOT force (1): (1)/(3) stays an independent "
          f"hypothesis, and the printed coprimality clause is not automatic")
    return True


def check_redflag_n_prime():
    """RED FLAG 1: n primality is load-bearing. For composite n the steps
    "C(n,k) = 0 mod n" and "x^(n-1) = 1 mod n" fail, and c'^n - 1 = 0 mod n
    does NOT give c' = 1 + n k_3."""
    for n in (4, 6, 9, 15):
        assert not sympy.isprime(n), "composite by construction"
        assert any(math.comb(n, k) % n != 0 for k in range(1, n)), \
            f"red flag: C({n},k) = 0 mod n fails"
        assert any(x for x in range(2, n)
                   if math.gcd(x, n) == 1 and (x ** (n - 1) - 1) % n != 0), \
            f"red flag: FLT mod n fails for composite n = {n}"
    assert (3 ** 4 - 1) % 4 == 0 and 3 % 4 != 1, \
        "red flag: n=4, c'=3 has c'^4 = 1 mod 4 but c' != 1 mod 4"
    assert (5 ** 6 - 1) % 6 == 0 and 5 % 6 != 1, \
        "red flag: n=6, c'=5 has c'^6 = 1 mod 6 but c' != 1 mod 6"
    print("red flag n prime ok (composite n: C(n,k) = 0 mod n and "
          "x^(n-1) = 1 mod n fail; n=4 c'=3 resp. n=6 c'=5 have c'^n = 1 mod n "
          "but c' != 1 mod n, so S9/S10 needs primality)")
    return True


def check_redflag_n_odd():
    """RED FLAG 2: "n la so nguyen to le" -- the oddness half is
    load-bearing for S12: halving 2(u+v-t) = 0 mod n^2 needs
    gcd(2, n^2) = 1. For the only even prime n = 2 it fails."""
    n = 2
    X = 2
    assert (2 * X) % (n * n) == 0 and X % (n * n) != 0, \
        "red flag: n=2: 2X = 0 mod 4 does not give X = 0 mod 4"
    for n in N_SET:
        assert all(X % (n * n) == 0 for X in range(-30, 31) if (2 * X) % (n * n) == 0), \
            "n odd: 2X = 0 mod n^2 => X = 0 mod n^2"
    print("red flag n odd ok (n = 2: 2X = 0 mod n^2 does not give X = 0 mod n^2, "
          "so the halving step S12/S22 needs n odd; holds for n in "
          f"{N_SET})")
    return True


def check_redflag_abc_not_divisible():
    """RED FLAG 3: the conclusion's "a, b, c, k khong chia het cho n" is
    load-bearing for the printed "nen s >= 2" (S13/S23). With n not dividing
    abck, v_n(n^s abck) = s, so n^2 | u+v-t forces s >= 2; once a factor is
    divisible by n the same representation admits s = 1 with n^2 | u+v-t."""
    for n in N_SET:
        assert (n ** 1 * n) % (n * n) == 0 and v_p(n ** 1 * n, n) == 2, \
            "abc = n: s = 1 already gives n^2 | n^s abc, i.e. s >= 2 fails"
        assert (n ** 1 * 1) % (n * n) != 0 and v_p(n ** 1 * 1, n) == 1, \
            "abc = 1: s = 1 does NOT give n^2 | n^s abc"
    n = 5
    a, b, c, k, s = n, 1, 1, 1, 1          # a divisible by n
    X = n ** s * a * b * c * k
    assert X == n * n and X % (n * n) == 0, "constructed u+v-t = n^2"
    assert s < 2, "red flag: s = 1 < 2 when a is divisible by n"
    print("red flag a,b,c not divisible by n ok (n = 5, s = 1, a = 5, b = c = k = 1: "
          "u+v-t = 25 = n^2 is divisible by n^2 although s = 1 < 2, so the printed "
          "'nen s >= 2' needs n not dividing abck)")
    return True


def check_redflag_uv_not_divisible():
    """RED FLAG 4: "uv khong chia het cho n" is load-bearing. It is what
    makes n not divide u and v (n prime); the proof then derives
    (t-u) not divisible by n and (t-v) not divisible by n in BOTH branches
    (p. 4, 6.1 and 6.2) and applies bo de 5a)/bo de 3. If n | a (a step of
    the conclusion's own "khong chia het cho n"), then t - u = a^n is
    divisible by n and that inference is unavailable."""
    n = 5
    a = n                                   # a divisible by n
    assert a ** n % n == 0, "n | a^n"
    assert n ** n % n == 0, "t - u = a^n is then divisible by n"
    t, u = n ** n + 1, 1
    assert (t - u) % n == 0 and u % n != 0, \
        "red flag: (t-u) divisible by n with n not dividing u (n | a)"
    for n in N_SET:
        for a in range(-3, 4):
            if a % n == 0:
                assert (a ** n) % n == 0, "n | a => n | a^n"
            else:
                assert (a ** n) % n != 0, "n not dividing a => n not dividing a^n"
    print("red flag uv not divisible by n ok (n = 5, a = 5: t - u = a^n = 3125 "
          "is divisible by n, so the '(t-u) khong chia het cho n' fact used by "
          "6.1 and 6.2 needs n not dividing a, which the hypothesis uv not "
          "divisible by n (n prime) supplies)")
    return True


def main():
    try:
        ok = (check_vacuity()
              and check_factorisations()
              and check_61_head()
              and check_61_flt()
              and check_61_cprime_identity()
              and check_61_cprime_congruence()
              and check_61_nsquare()
              and check_param_shape()
              and check_62_algebra()
              and check_621_k0()
              and check_conclusion_shape()
              and check_redflag_n_prime()
              and check_redflag_n_odd()
              and check_redflag_abc_not_divisible()
              and check_redflag_uv_not_divisible())
    except AssertionError as e:
        print(f"L6 SMOKE FAIL: {e}")
        return 1
    print("L6 SMOKE PASS" if ok else "L6 SMOKE FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
