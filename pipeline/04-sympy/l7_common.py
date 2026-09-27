"""Shared witness search for bổ đề 7's remaining conclusion groups.

Chunks L7-FRAG-02 … L7-FRAG-06 (and the section assembly L7-ASM) are screened
on REAL instances: bổ đề 7's hypotheses are satisfiable (they are congruences,
not a Fermat equation), so unlike L1/L2/L6 no vacuity note is needed — the
screen below finds witnesses and checks every claimed conclusion on them.

A witness for prime `n` is a triple (a, b, c) with 1 <= a, b, c < n²,
n ∤ a*b*c, and

    a^n + b^n ≡ c^n                      (mod n²)        [GT2]
    a^{n(n−2)} + b^{n(n−2)} ≡ c^{n(n−2)} (mod n)         [GT3]

(the second is derivable from the first, but it is a hypothesis of the lemma,
so it is enforced here too). The search is a table join: c is looked up by its
n-th power residue, so it is O(n²) per prime, not O(n⁶).

Every assertion is a *conclusion* the chunk claims, evaluated modulo n² or n
as the display says — a counterexample means the transcription (or the
printed statement) is wrong, and the chunk must not be formalized.
"""
from __future__ import annotations

PRIMES = (5, 7, 11, 13)


def witnesses(n: int) -> list[tuple[int, int, int]]:
    """All (a, b, c) satisfying bổ đề 7's three hypotheses (mod n² / mod n)."""
    n2 = n * n
    pw = [pow(i, n, n2) for i in range(n2)]              # i^n mod n²
    pw2 = [pow(i, n * (n - 2), n) for i in range(n2)]    # i^{n(n-2)} mod n
    by_cn: dict[int, list[int]] = {}
    for c in range(1, n2):
        if c % n == 0:
            continue
        by_cn.setdefault(pw[c], []).append(c)
    out: list[tuple[int, int, int]] = []
    for a in range(1, n2):
        if a % n == 0:
            continue
        for b in range(1, n2):
            if b % n == 0:
                continue
            for c in by_cn.get((pw[a] + pw[b]) % n2, ()):
                if (pw2[a] + pw2[b] - pw2[c]) % n == 0:
                    out.append((a, b, c))
    return out


def run(assertions: dict, primes=PRIMES, extra=None) -> int:
    """Check `assertions` (name -> f(a,b,c,n) -> bool) on every witness.

    `extra` is an optional list of (name, callable returning (ok, detail))
    checks that do not depend on a witness (red flags, algebraic step screens).
    Prints a per-prime tally; returns 0 when nothing failed.
    """
    total_w = 0
    failures: list[str] = []
    for n in primes:
        w = witnesses(n)
        total_w += len(w)
        print(f"n={n}: {len(w)} witness(es)")
        for a, b, c in w:
            for name, fn in assertions.items():
                if not fn(a, b, c, n):
                    failures.append(f"n={n} (a,b,c)=({a},{b},{c}): {name} FAILED")
    for obj in extra or []:
        name, fn = obj
        ok, detail = fn()
        print(f"  [extra] {name}: {'ok' if ok else 'FAILED'} — {detail}")
        if not ok:
            failures.append(f"{name} FAILED — {detail}")
    if total_w == 0:
        print("NO WITNESSES at these primes — screen is vacuous, check the search")
        return 1
    if failures:
        print(f"{len(failures)} failure(s):")
        for f in failures[:20]:
            print("   ", f)
        print("COUNTEREXAMPLE FOUND — chunk is wrong, do not formalize")
        return 1
    print(f"smoke OK — {total_w} real instances, all assertions hold")
    return 0


# --- the claims, as lambdas over a witness (n² denotes n**2) -----------------

def n2(n):  # noqa: D103 - tiny alias
    return n * n


CLAIMS = {
    "S0/5d c^{n(n-1)} = 1": lambda a, b, c, n: pow(c, n * (n - 1), n2(n)) == 1,
    "(a) a^{n2}+b^{n2}-c^{n2} = 0": lambda a, b, c, n: (
        pow(a, n * n, n2(n)) + pow(b, n * n, n2(n)) - pow(c, n * n, n2(n))
    ) % n2(n) == 0,
    "(b) c^n = a^n+b^n": lambda a, b, c, n: (
        pow(c, n, n2(n)) - pow(a, n, n2(n)) - pow(b, n, n2(n))
    ) % n2(n) == 0,
    "(c) c^{n(n-2)} = a^{..}+b^{..} mod n": lambda a, b, c, n: (
        pow(c, n * (n - 2), n) - pow(a, n * (n - 2), n) - pow(b, n * (n - 2), n)
    ) % n == 0,
    "(d) a^n b^n = c^{2n} mod n": lambda a, b, c, n: (
        pow(a, n, n) * pow(b, n, n) - pow(c, 2 * n, n)
    ) % n == 0,
    "S5 b^{2n}+a^n c^n = 0 mod n": lambda a, b, c, n: (
        pow(b, 2 * n, n) + pow(a, n, n) * pow(c, n, n)
    ) % n == 0,
    "S6 b^{3n}+c^{3n} = 0 mod n": lambda a, b, c, n: (
        pow(b, 3 * n, n) + pow(c, 3 * n, n)
    ) % n == 0,
    "(19/5.9) b^{3n}+c^{3n} = 0": lambda a, b, c, n: (
        pow(b, 3 * n, n2(n)) + pow(c, 3 * n, n2(n))
    ) % n2(n) == 0,
    "(20/5.10) a^{3n}-b^{3n} = 0": lambda a, b, c, n: (
        pow(a, 3 * n, n2(n)) - pow(b, 3 * n, n2(n))
    ) % n2(n) == 0,
    "(5.10) a^{3n}+c^{3n} = 0": lambda a, b, c, n: (
        pow(a, 3 * n, n2(n)) + pow(c, 3 * n, n2(n))
    ) % n2(n) == 0,
    "(18) a^{2n}+b^n c^n = 0": lambda a, b, c, n: (
        pow(a, 2 * n, n2(n)) + pow(b, n, n2(n)) * pow(c, n, n2(n))
    ) % n2(n) == 0,
    "(18) b^{2n}+a^n c^n = 0": lambda a, b, c, n: (
        pow(b, 2 * n, n2(n)) + pow(a, n, n2(n)) * pow(c, n, n2(n))
    ) % n2(n) == 0,
    "(18) c^{2n}-a^n b^n = 0": lambda a, b, c, n: (
        pow(c, 2 * n, n2(n)) - pow(a, n, n2(n)) * pow(b, n, n2(n))
    ) % n2(n) == 0,
    "(22') a^{n(n-2)}+b^{n(n-2)}-c^{n(n-2)} = 0": lambda a, b, c, n: (
        pow(a, n * (n - 2), n2(n)) + pow(b, n * (n - 2), n2(n))
        - pow(c, n * (n - 2), n2(n))
    ) % n2(n) == 0,
    "(21) a^{n(n-4)}+c^{n(n-4)} = 0": lambda a, b, c, n: (
        pow(a, n * (n - 4), n2(n)) + pow(c, n * (n - 4), n2(n))
    ) % n2(n) == 0,
    "(21) b^{n(n-4)}+c^{n(n-4)} = 0": lambda a, b, c, n: (
        pow(b, n * (n - 4), n2(n)) + pow(c, n * (n - 4), n2(n))
    ) % n2(n) == 0,
    "(21) a^{n(n-4)}-b^{n(n-4)} = 0": lambda a, b, c, n: (
        pow(a, n * (n - 4), n2(n)) - pow(b, n * (n - 4), n2(n))
    ) % n2(n) == 0,
    "(22) a^{n(n-3)}+b^{n(n-3)}+c^{n(n-3)} = 0": lambda a, b, c, n: (
        pow(a, n * (n - 3), n2(n)) + pow(b, n * (n - 3), n2(n))
        + pow(c, n * (n - 3), n2(n))
    ) % n2(n) == 0,
    "n = 1 (mod 6)": lambda a, b, c, n: n % 6 == 1,
}


def reductio_screen(primes=(5, 11, 17, 23)) -> tuple[bool, str]:
    """S16's substitution step, screened on instances of (19)+(20)+GT3':

    for n ≡ 5 (mod 6) (so n − 2 = 3·(2l−1) with 2l−1 odd =: k), pick (a, b, c)
    with n ∤ a, b^{3n} ≡ a^{3n} and c^{3n} ≡ −a^{3n} (mod n²); the print claims
    the sum a^{n(n−2)}+b^{n(n−2)}−c^{n(n−2)} then collapses to 3a^{n(n−2)}.
    """
    checked = 0
    bad = []
    for n in primes:
        if n % 6 != 5:
            continue
        n2_ = n * n
        k = (n - 2) // 3
        if (n - 2) % 3 != 0 or k % 2 == 0:
            bad.append(f"n={n}: k={k} not odd")
            continue
        p3 = [pow(i, 3 * n, n2_) for i in range(n2_)]
        by3: dict[int, list[int]] = {}
        for i in range(1, n2_):
            if i % n == 0:
                continue
            by3.setdefault(p3[i], []).append(i)
        for a in range(1, n2_):
            if a % n == 0:
                continue
            bs = by3.get(p3[a], [])
            cs = by3.get((-p3[a]) % n2_, [])
            if not bs or not cs:
                continue
            b, c = bs[0], cs[0]
            checked += 1
            lhs = (pow(a, n * (n - 2), n2_) + pow(b, n * (n - 2), n2_)
                   - pow(c, n * (n - 2), n2_)) % n2_
            if lhs != 3 * pow(a, n * (n - 2), n2_) % n2_:
                bad.append(f"n={n} a={a}: sum={lhs} != 3a^{{n(n-2)}}")
    if bad:
        return False, f"{len(bad)} instance(s) break the substitution: {bad[:3]}"
    return True, f"{checked} (a,b,c) instances of (19)/(20) with n ≡ 5 (mod 6)"
