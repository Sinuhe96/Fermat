"""Stage 4 smoke for chunk L5-01 (bo de 5).

Method note (contrast with L1-01 / L2-01): bo de 5's hypotheses ARE
satisfiable -- `n` an odd prime and `u, v` coprime integers (e.g. n = 5,
u = 1, v = 4) -- so this is an INSTANCE-BASED screen on real integers,
not a vacuity note.  It remains a smoke screen, not a proof: exit 0 only
means "no transcription red flag on the searched range"; nothing here is
a claim beyond the searched box and the symbolic identities below.

Lemma 5 (PROOF_of_FERMAT.pdf p1, region P001-R3), with
  A := sum_{i=0}^{n-1} (-1)^i u^{n-1-i} v^i :
  a) (u+v) not divisible by n  =>  (u+v, A) = 1  and  A not divisible by n
  b) (u+v) divisible by n      =>  (u+v, A) = n  and  A not divisible by n^2
  c) (u^n+v^n) divisible by n  =>  (u^n+v^n) divisible by n^2
     (the author explicitly drops the hypothesis (u,v) = 1 here)
  d) u not divisible by n      =>  u^{n(n-1)} = 1 (mod n^2)

What is screened:

  * the printed algebraic identities, symbolically (exact sympy.expand)
    and on integers -- a transcription slip in an exponent or a sign
    shows up here:
      - A = sum_{k=0}^{n-1} (-1)^k C_n^k (u+v)^{n-1-k} v^k   [P002-R2]
      - u^n + v^n = (u+v) * A                               [P002-R2]
      - A = (u+v)*sum_{k=0}^{n-2} (-1)^k C_n^k (u+v)^{n-2-k} v^k
            + n*v^{n-1}   (the k = n-1 term is +n*v^{n-1})   [P002-R2]
      - A = n(u+v)*A_1 + n*v^{n-1} with the printed
        A_1 = sum_{k=0}^{n-3} (-1)^k (C_n^k/n) (u+v)^{n-2-k} v^k
              - ((n-1)/2) * v^{n-2}                          [P003-R1]
        The sign of that second bracket term is exactly where a
        transcription slip would sit: it comes from the k = n-2 term
        (-1)^{n-2} * C_n^{n-2} * v^{n-2}, i.e. (-1)^{n-2} = -1 for odd n.
        check_b_identity_symbolic asserts that arithmetical origin
        explicitly as well as the finished identity.
  * a), b), c), d) on real integer instances; both branches of c)'s case
    split (uv divisible by n / uv not divisible by n) and, inside the
    second branch, both sub-cases ((u+v) divisible / not divisible by n).
  * four red-flag checks that a stated hypothesis is load-bearing:
      F1 "n la so nguyen to" in a) and c) -- composite odd n refutes both;
      F2 "(u,v) = 1" in a)     -- non-coprime u, v break (u+v, A) = 1;
      F3 "n le" (n odd) in the shared expansion u^n+v^n = (u+v)A;
      F4 "(u,v) = 1" in b)     -- non-coprime u, v break (u+v, A) = n.

n ranges over {5, 7, 11, 13} (schema criterion 2) plus the small case
n = 3, which is itself a legitimate instance of the lemma (3 is an odd
prime).  n = 1 is used ONLY in the identity checks: n = 1 is not prime,
so a)/b)/c)'s hypotheses degenerate there ((u+v) is always divisible by
1, nothing is "u not divisible by 1") and the a) gcd claim is not the
lemma's claim; that degeneracy is the reason the schema's required set
starts at 5 and the author's "n nguyen to le" is load-bearing.

Printed-proof note (recorded, not a screen failure).  Part a)'s statement
has TWO conjuncts, but the a) proof text ends "(dpcm)" immediately after
"(u+v, n v^{n-1}) = 1, suy ra (A, u+v) = 1": it visibly derives
gcd(u+v, A) = 1 only.  The second conjunct (A not divisible by n) is a
true statement and this screen verifies it on instances, and the same
mod-n technique is used in c) -- but as printed, a) states it without
deriving it.  Flagged for the Lean lane (the F3/F4 watch-list).
"""

import math
import sys
from itertools import product

import sympy

N_SMALL = (1, 3)                 # n = 3 is a real instance; n = 1 identities only
N_REQUIRED = (5, 7, 11, 13)      # schema criterion 2
N_IDENT = N_SMALL + N_REQUIRED   # identities are checked on all of these
N_ODD = (3, 5, 7, 11, 13)        # n >= 3 odd: the b) bracket needs v^{n-2}


def num_A(u, v, n):
    """A = sum_{i=0}^{n-1} (-1)^i u^{n-1-i} v^i  (exact Python ints)."""
    return sum((-1) ** i * u ** (n - 1 - i) * v ** i for i in range(n))


def coprime(u, v):
    return math.gcd(abs(u), abs(v)) == 1


def printed_A1(u, v, n):
    """The A_1 printed in b) (region P003-R1), exact rational value."""
    s = sum(sympy.Rational((-1) ** k * sympy.binomial(n, k), n)
            * (u + v) ** (n - 2 - k) * v ** k for k in range(n - 2))
    return s - sympy.Rational(n - 1, 2) * v ** (n - 2)


# --------------------------------------------------------------------------
# printed identities
# --------------------------------------------------------------------------

def check_identities_symbolic(n_set=N_IDENT):
    """Exact symbolic check of the three identities printed in P002-R2."""
    x, y = sympy.symbols("x y")
    for n in n_set:
        A = sum((-1) ** i * x ** (n - 1 - i) * y ** i for i in range(n))
        B = sum((-1) ** k * sympy.binomial(n, k) * (x + y) ** (n - 1 - k) * y ** k
                for k in range(n))
        assert sympy.expand(A - B) == 0, f"identity A = sum_k (-1)^k C_n^k FAIL n={n}"
        B2 = ((x + y) * sum((-1) ** k * sympy.binomial(n, k)
                            * (x + y) ** (n - 2 - k) * y ** k for k in range(n - 1))
              + n * y ** (n - 1))
        assert sympy.expand(B - B2) == 0, f"k=n-1 split FAIL n={n}"
        if n % 2 == 1:
            assert sympy.expand(x ** n + y ** n - (x + y) * B) == 0, \
                f"setup u^n+v^n = (u+v)A FAIL n={n}"
    print(f"identities ok (exact symbolic, n in {n_set}): A = sum_k (-1)^k C_n^k "
          "(u+v)^{n-1-k} v^k; u^n+v^n = (u+v)A for odd n; and the k=n-1 term "
          "is +n*v^{n-1}")
    return True


def check_b_identity_symbolic(n_set=N_ODD):
    """Exact check of the b) decomposition, plus the arithmetical origin of
    the printed `- (n-1)v^{n-2}/2`: the k = n-2 term of the (u+v)-factored
    sum is (-1)^{n-2} C_n^{n-2} v^{n-2} = -n * ((n-1)/2) v^{n-2} for odd n."""
    x, y = sympy.symbols("x y")
    for n in n_set:
        A = sum((-1) ** i * x ** (n - 1 - i) * y ** i for i in range(n))
        A1 = (sum((-1) ** k * sympy.Rational(sympy.binomial(n, k), n)
                  * (x + y) ** (n - 2 - k) * y ** k for k in range(n - 2))
              - sympy.Rational(n - 1, 2) * y ** (n - 2))
        assert sympy.expand(A - (n * (x + y) * A1 + n * y ** (n - 1))) == 0, \
            f"b) A = n(u+v)A_1 + n v^{n-1} FAIL n={n}"
        # the k = n-2 term, and hence the printed sign:
        term = (-1) ** (n - 2) * sympy.binomial(n, n - 2) * y ** (n - 2)
        assert sympy.expand(term - n * (-sympy.Rational(n - 1, 2)) * y ** (n - 2)) == 0, \
            f"k=n-2 sign FAIL n={n}"
        assert (n - 2) % 2 == 1, f"n odd not used for the sign n={n}"
    print(f"b) identity ok (exact symbolic, n in {n_set}): A = n(u+v)A_1 + n*v^(n-1) "
          "with the printed A_1; the k=n-2 term is (-1)^{n-2}*C_n^{n-2}*v^{n-2} "
          "= -n*((n-1)/2)*v^{n-2}, i.e. the printed bracket sign is right")
    return True


def check_identities_numeric(n_set=N_IDENT, limit=7):
    """The same identities on real integers, including negative u, v."""
    checked = 0
    for n in n_set:
        for u, v in product(range(-limit, limit + 1), repeat=2):
            if u == 0 or v == 0 or u + v == 0:
                continue
            A = num_A(u, v, n)
            assert A * (u + v) == u ** n + v ** n, \
                f"numeric u^n+v^n = (u+v)A FAIL n={n} {(u, v)}"
            if n % 2 == 1:
                assert (u ** n + v ** n) % (u + v) == 0 and \
                       (u ** n + v ** n) // (u + v) == A, \
                    f"numeric quotient FAIL n={n} {(u, v)}"
            checked += 1
    print(f"identities ok ({checked} integer instances: A*(u+v) = u^n+v^n and, "
          "for odd n, A = (u^n+v^n)/(u+v))")
    return True


# --------------------------------------------------------------------------
# a), b), c), d) on real instances
# --------------------------------------------------------------------------

def check_a(n_set=(3, 5, 7, 11, 13), limit=14):
    """a) on real (u,v): (u,v) = 1 and n does not divide u+v  =>
    (u+v, n v^{n-1}) = 1, hence (u+v, A) = 1; also A is not divisible by n
    (the statement's second conjunct -- stated, see the module docstring)."""
    hits = {}
    for n in n_set:
        hit = 0
        for u, v in product(range(-limit, limit + 1), repeat=2):
            if u == 0 or v == 0 or u + v == 0:
                continue
            if not coprime(u, v):
                continue
            if (u + v) % n == 0:          # a)'s hypothesis: (u+v) not divisible by n
                continue
            g = math.gcd(abs(u + v), abs(n * v ** (n - 1)))
            assert g == 1, f"a) FAIL (u+v, n v^(n-1)) = 1, n={n} {(u, v)}"
            A = num_A(u, v, n)
            assert math.gcd(abs(u + v), abs(A)) == 1, \
                f"a) FAIL (u+v, A) = 1, n={n} {(u, v)}"
            assert A % n != 0, f"a) FAIL A not divisible by n, n={n} {(u, v)}"
            hit += 1
        assert hit > 0, f"a) screen vacuous for n={n}"
        hits[n] = hit
    print(f"a) ok ({hits} real instances with (u,v)=1, n∤(u+v): "
          "(u+v, n v^(n-1)) = 1 => (u+v, A) = 1 and n∤A)")
    return True


def check_b(n_set=N_ODD, limit=16):
    """b) on real (u,v): (u,v) = 1 and n | u+v  =>  A = n(u+v)A_1 + n v^{n-1}
    with n(u+v)A_1 divisible by n^2 and n v^{n-1} divisible by n but not by
    n^2 (as n does not divide v), hence A divisible by n, not by n^2, and
    (u+v, A) = n."""
    hits = {}
    for n in n_set:
        hit = 0
        for u, v in product(range(-limit, limit + 1), repeat=2):
            if u == 0 or v == 0 or u + v == 0:
                continue
            if not coprime(u, v):
                continue
            if (u + v) % n != 0:          # b)'s hypothesis: u+v divisible by n
                continue
            assert v % n != 0, f"b) FAIL v not divisible by n, n={n} {(u, v)}"
            A = num_A(u, v, n)
            # the printed A_1, exactly:
            A1 = printed_A1(u, v, n)
            assert n * (u + v) * A1 + n * v ** (n - 1) == A, \
                f"b) FAIL printed A_1 decomposition, n={n} {(u, v)}"
            lhs = n * (u + v) * A1        # = n(u+v)A_1, an integer
            assert lhs.q == 1, f"b) FAIL n(u+v)A_1 not integral, n={n} {(u, v)}"
            assert int(lhs) % (n * n) == 0, \
                f"b) FAIL n(u+v)A_1 divisible by n^2, n={n} {(u, v)}"
            assert (n * v ** (n - 1)) % n == 0 and \
                   (n * v ** (n - 1)) % (n * n) != 0, \
                f"b) FAIL n v^(n-1) divisible by n, not n^2, n={n} {(u, v)}"
            assert A % n == 0, f"b) FAIL A divisible by n, n={n} {(u, v)}"
            assert A % (n * n) != 0, f"b) FAIL A not divisible by n^2, n={n} {(u, v)}"
            assert math.gcd(abs(u + v), abs(A)) == n, \
                f"b) FAIL (u+v, A) = n, n={n} {(u, v)}"
            hit += 1
        assert hit > 0, f"b) screen vacuous for n={n}"
        hits[n] = hit
    print(f"b) ok ({hits} real instances with (u,v)=1, n|(u+v): printed A_1 exact, "
          "n(u+v)A_1 ⋮ n^2, n v^(n-1) ⋮ n but ⋮̸ n^2, A ⋮ n but ⋮̸ n^2, (u+v,A) = n)")
    return True


def check_c(n_set=(3, 5, 7, 11, 13), limit=18):
    """c) on real instances, BOTH branches of the case split and BOTH
    sub-cases of the second branch.  (u,v) = 1 is deliberately NOT assumed
    (the lemma says it is not needed for c)."""
    branch1 = {}     # uv ⋮ n
    branch2a = {}    # uv ⋮̸ n and (u+v) ⋮ n
    fallen = 0       # uv ⋮̸ n and (u+v) ⋮̸ n with n | u^n+v^n: must stay empty
    for n in n_set:
        b1 = b2a = 0
        for u, v in product(range(-limit, limit + 1), repeat=2):
            if u == 0 or v == 0:
                continue
            s = u ** n + v ** n
            if u % n and v % n:                       # uv ⋮̸ n
                # Fermat's little theorem step used by the author:
                assert (u ** (n - 1) - 1) % n == 0 and (v ** (n - 1) - 1) % n == 0, \
                    f"c) FAIL FLT residues, n={n} {(u, v)}"
                if (u + v) % n:
                    # the author's mod-n evaluation of A, hence n ∤ s = (u+v)A:
                    assert num_A(u, v, n) % n == 1, \
                        f"c) FAIL A = 1 (mod n), n={n} {(u, v)}"
                    if s % n == 0:
                        fallen += 1
                    continue
                if s % n == 0:
                    b2a += 1
                    # (u+v) ⋮ n gives A ⋮ n (A = (u+v)*B + n v^(n-1)), hence n^2 | s
                    assert num_A(u, v, n) % n == 0
            else:                                      # uv ⋮ n
                if s % n == 0:
                    b1 += 1
            if s % n != 0:
                continue
            assert s % (n * n) == 0, f"c) FAIL n^2 | u^n+v^n, n={n} {(u, v)}"
        assert b1 > 0 and b2a > 0, f"c) screen vacuous for n={n} (uv⋮n={b1}, uv⋮̸n={b2a})"
        branch1[n], branch2a[n] = b1, b2a
    assert fallen == 0, f"c) FAIL: {(fallen)} instances with n∤uv, n∤(u+v), n | u^n+v^n"
    print(f"c) ok (uv ⋮ n branch {branch1}, uv ⋮̸ n branch with (u+v) ⋮ n {branch2a}; "
          "every (u^n+v^n) ⋮ n instance also has n^2 | u^n+v^n, and the "
          "uv ⋮̸ n, (u+v) ⋮̸ n sub-case is empty because there A = 1 (mod n))")
    return True


def check_d(n_set=(3, 5, 7, 11, 13), limit=20):
    """d) on real u: n prime and n ∤ u  =>  u^{n-1} = 1 + m n with m >= 0,
    hence u^{n(n-1)} = (1+mn)^n = 1 (mod n^2)."""
    hits = {}
    for n in n_set:
        hit = 0
        for u in range(-limit, limit + 1):
            if u == 0 or u % n == 0:      # d)'s hypothesis: u not divisible by n
                continue
            assert (u ** (n - 1) - 1) % n == 0, f"d) FAIL FLT n={n} u={u}"
            m = (u ** (n - 1) - 1) // n
            assert m >= 0, f"d) FAIL m >= 0 n={n} u={u}"
            assert (1 + m * n) ** n == u ** (n * (n - 1)), f"d) FAIL re-power n={n} u={u}"
            assert (u ** (n * (n - 1)) - 1) % (n * n) == 0, \
                f"d) FAIL u^{n(n-1)} = 1 (mod n^2) n={n} u={u}"
            hit += 1
        assert hit > 0, f"d) screen vacuous for n={n}"
        hits[n] = hit
    print(f"d) ok ({hits} real u with n ∤ u: u^(n-1) = 1+mn with m >= 0 and "
          "u^{n(n-1)} = (1+mn)^n = 1 (mod n^2))")
    return True


# --------------------------------------------------------------------------
# red flags: stated hypotheses that are load-bearing
# --------------------------------------------------------------------------

def flag_n_prime(n=9, u=1, v=2):
    """RED FLAG (a) and c): drop "n is prime".  For composite odd n = 9,
    (u,v) = 1 and 9 ∤ u+v hold, yet (u+v, A) != 1; and 9 | u^9+v^9 while
    81 ∤ u^9+v^9, refuting c).  So "n nguyen to" is load-bearing in both."""
    assert coprime(u, v) and (u + v) % n != 0, "primality probe drifted"
    g = math.gcd(abs(u + v), abs(num_A(u, v, n)))
    assert g != 1, "a) primality probe: expected (u+v, A) != 1 for n=9"
    s = u ** n + v ** n
    assert s % n == 0 and s % (n * n) != 0, "c) primality probe drifted"
    print(f"red flag ok: 'n prime' is needed -- n={n}, (u,v)=({u},{v}): (u+v,A) = {g} "
          f"!= 1 (a) fails) and {n} | {s} but {n * n} ∤ {s} (c) fails)")
    return True


def flag_coprime_in_a(n=5, u=2, v=4):
    """RED FLAG (a): drop "(u,v) = 1".  With (u,v) = 2, n = 5 ∤ u+v, the
    hypothesis (u+v, n v^{n-1}) = 1 already fails, and so does the stated
    conclusion (u+v, A) = 1."""
    assert math.gcd(u, v) == 2 and (u + v) % n != 0, "coprimality probe drifted"
    assert math.gcd(abs(u + v), abs(n * v ** (n - 1))) != 1, \
        "a) coprime probe: expected (u+v, n v^(n-1)) != 1"
    g = math.gcd(abs(u + v), abs(num_A(u, v, n)))
    assert g != 1, "a) coprime probe: expected (u+v, A) != 1"
    print(f"red flag ok: '(u,v) = 1' is needed in a) -- n={n}, (u,v)=({u},{v}), "
          f"u+v={u + v}, A={num_A(u, v, n)}: (u+v, A) = {g} != 1")
    return True


def flag_n_odd(n=4, u=1, v=2):
    """RED FLAG (shared setup): drop "n odd".  Then u^n + v^n = (u+v)A is
    false, and the k = n-1 term of the binomial sum is -n*v^{n-1}, not
    +n*v^{n-1}; the oddness is exactly what makes the two v^n terms cancel."""
    A = num_A(u, v, n)
    assert A * (u + v) != u ** n + v ** n, "oddness probe drifted"
    assert (-1) ** (n - 1) * sympy.binomial(n, n - 1) == -n != n, \
        "oddness probe: k=n-1 term sign"
    print(f"red flag ok: 'n le' is needed -- n={n}: (u+v)A = {(u + v) * A} != "
          f"u^n+v^n = {u ** n + v ** n}, and the k=n-1 term is -n*v^(n-1)")
    return True


def flag_coprime_in_b(n=5, u=2, v=8):
    """RED FLAG (b): drop "(u,v) = 1".  With (u,v) = 2 and n = 5 | u+v,
    A is still divisible by n (and not by n^2), but (u+v, A) = 10 != 5, so
    b)'s first conclusion needs the coprimality hypothesis."""
    assert math.gcd(u, v) == 2 and (u + v) % n == 0, "b) coprime probe drifted"
    A = num_A(u, v, n)
    assert A % n == 0 and A % (n * n) != 0, "b) coprime probe: divisibility drifted"
    g = math.gcd(abs(u + v), abs(A))
    assert g == 10 != n, "b) coprime probe: expected (u+v, A) = 10 for n=5"
    print(f"red flag ok: '(u,v) = 1' is needed in b) -- n={n}, (u,v)=({u},{v}), "
          f"u+v={u + v}, A={A}: (u+v, A) = {g} != {n}")
    return True


ok = (
    check_identities_symbolic()
    and check_b_identity_symbolic()
    and check_identities_numeric()
    and check_a()
    and check_b()
    and check_c()
    and check_d()
    and flag_n_prime()
    and flag_coprime_in_a()
    and flag_n_odd()
    and flag_coprime_in_b()
)
print("L5 SMOKE PASS" if ok else "L5 SMOKE FAIL")
sys.exit(0 if ok else 1)
