"""M1-FRAG-05 screen: the fifteen printed binomial-to-factorial conversions.

WHAT IS SCREENED. P007 prints the l+j <= 4 part of the triple sum of p. 6 as
FIFTEEN sums, one per pair (j,l) with j + l <= 4, each with the binomial
coefficients C(n-1-i,j)*C(i,l) rewritten in the author's factorial form
(e.g. C(i,4) = i(i-1)(i-2)(i-3)/24). The identity claimed by that display is

    sum_{i,j,l : j+l <= 4} (-1)^j C(n-1-i,j) C(i,l) h^(n-1-i-j) b^(n(i-l)) X^(l+j)
      = sum over the same fifteen (j,l) of  [printed coefficient]
                                             * [printed polynomial in i]
                                             * h^(printed h exponent)
                                             * b^(printed b index)
                                             * X^(l+j),

with X = n^s*a*b*c*k. The screen evaluates BOTH sides term by term (exact
integers) at concrete parameters and compares each pair separately, so a
discrepancy is localised to the pair that carries it.

WHAT THE PRINTED FORMS ARE. Byte-copied from the signed region records
01-extract/regions/p007.yml (R1 l6-l7 = the five X^4 sums, R2 l0-l1 = the four
X^3 sums, R2 l2 = the three X^2 sums, R2 l3 = the two X^1 sums and the X^0 sum);
the binomial side is p006.yml R3 l2-l4. Both regions are REVIEWED/signed, and
the two crops page-007-300dpi-region-02.png / -03.png were read again by vision
on 2026-09-28 and agree with the text layer.

RESULT. Fourteen of the fifteen pairs agree exactly. The pair (j,l) = (2,1) --
the FIRST sum printed in the X^3 group, printed identically at P007-R2 l0 and
again at P007-R3 l2 -- is printed WITHOUT its denominator 2:

    binomial side : (-1)^2 C(n-1-i,2) C(i,1) = i(n-1-i)(n-2-i)/2
    printed side  :                             i(n-1-i)(n-2-i)

so the printed display overstates that one sum by a factor of 2. This is the
finding behind query Q-005, not a transcription error of ours.

EXIT CODE. 0 iff the finding reproduces exactly: every pair matches except
(2,1), whose printed value is precisely 2x the binomial value. Any other
outcome is exit 1 (the finding is wrong, or the screen itself is).

Run:  docker compose exec -T lean python /workspace/pipeline/04-sympy/m1f5_screen.py
"""
from __future__ import annotations

from fractions import Fraction
from math import comb

# (j, l, printed coefficient, printed polynomial in (n,i), printed h exponent,
#  printed b index, printed i-range) -- transcription of the p. 7 display.
# poly is given as a function of (n, i); bidx is the index inside b^(n*bidx).
PRINTED = [
    # --- the five X^4 sums, P007-R1 l6-l7, in the printed order ---
    (0, 4, Fraction(1, 24), lambda n, i: i * (i - 1) * (i - 2) * (i - 3),
     lambda n, i: n - 1 - i, lambda n, i: i - 4, lambda n: (4, n - 1)),
    (4, 0, Fraction(1, 24),
     lambda n, i: (n - 1 - i) * (n - 2 - i) * (n - 3 - i) * (n - 4 - i),
     lambda n, i: n - 5 - i, lambda n, i: i, lambda n: (0, n - 5)),
    (3, 1, Fraction(-1, 6),
     lambda n, i: i * (n - 1 - i) * (n - 2 - i) * (n - 3 - i),
     lambda n, i: n - 4 - i, lambda n, i: i - 1, lambda n: (1, n - 4)),
    (1, 3, Fraction(-1, 6),
     lambda n, i: (n - 1 - i) * i * (i - 1) * (i - 2),
     lambda n, i: n - 2 - i, lambda n, i: i - 3, lambda n: (3, n - 2)),
    (2, 2, Fraction(1, 4),
     lambda n, i: (n - 1 - i) * (n - 2 - i) * i * (i - 1),
     lambda n, i: n - 3 - i, lambda n, i: i - 2, lambda n: (2, n - 3)),
    # --- the four X^3 sums, P007-R2 l0-l1 ---
    (2, 1, Fraction(1), lambda n, i: i * (n - 1 - i) * (n - 2 - i),
     lambda n, i: n - 3 - i, lambda n, i: i - 1, lambda n: (1, n - 3)),
    (1, 2, Fraction(-1, 2), lambda n, i: i * (i - 1) * (n - 1 - i),
     lambda n, i: n - 2 - i, lambda n, i: i - 2, lambda n: (2, n - 2)),
    (3, 0, Fraction(-1, 6),
     lambda n, i: (n - 1 - i) * (n - 2 - i) * (n - 3 - i),
     lambda n, i: n - 4 - i, lambda n, i: i, lambda n: (0, n - 4)),
    (0, 3, Fraction(1, 6), lambda n, i: i * (i - 1) * (i - 2),
     lambda n, i: n - 1 - i, lambda n, i: i - 3, lambda n: (3, n - 1)),
    # --- the three X^2 sums, P007-R2 l2 ---
    (0, 2, Fraction(1, 2), lambda n, i: i * (i - 1),
     lambda n, i: n - 1 - i, lambda n, i: i - 2, lambda n: (2, n - 1)),
    (2, 0, Fraction(1, 2), lambda n, i: (n - 1 - i) * (n - 2 - i),
     lambda n, i: n - 3 - i, lambda n, i: i, lambda n: (0, n - 3)),
    (1, 1, Fraction(-1), lambda n, i: i * (n - 1 - i),
     lambda n, i: n - 2 - i, lambda n, i: i - 1, lambda n: (1, n - 2)),
    # --- the two X^1 sums and the X^0 sum, P007-R2 l3 ---
    (0, 1, Fraction(1), lambda n, i: i,
     lambda n, i: n - 1 - i, lambda n, i: i - 1, lambda n: (1, n - 1)),
    (1, 0, Fraction(-1), lambda n, i: (n - 1 - i),
     lambda n, i: n - 2 - i, lambda n, i: i, lambda n: (0, n - 2)),
    (0, 0, Fraction(1), lambda n, i: 1,
     lambda n, i: n - 1 - i, lambda n, i: i, lambda n: (0, n - 1)),
]


def binom_side(n: int, j: int, l: int, h: int, b: int, X: int) -> int:
    """The (j,l) sum of the p. 6 triple sum, exactly, with all factors kept."""
    total = 0
    for i in range(l, n - 1 - j + 1):          # printed range i in [l, n-1-j]
        total += ((-1) ** j) * comb(n - 1 - i, j) * comb(i, l) \
            * h ** (n - 1 - i - j) * b ** (n * (i - l)) * X ** (l + j)
    return total


def printed_side(n: int, row, h: int, b: int, X: int):
    """The same (j,l) sum as the p. 7 display writes it, as an exact Fraction."""
    j, l, coeff, poly, hexp, bidx, rng = row
    lo, hi = rng(n)
    total = Fraction(0)
    for i in range(lo, hi + 1):
        he, bi = hexp(n, i), bidx(n, i)
        if he < 0 or bi < 0:                   # range must make them non-negative
            raise AssertionError(f"negative exponent at (j,l)=({j},{l}), i={i}")
        total += coeff * poly(n, i) * Fraction(h ** he * b ** (n * bi) * X ** (l + j))
    return total


def screen(n: int, a: int, b: int, c: int, k: int, h: int, s: int = 1, verbose=True):
    """Compare all fifteen pairs at one parameter set; return the mismatches."""
    X = (n ** s) * a * b * c * k
    mismatches, ratio_ok = [], 0
    for row in PRINTED:
        j, l = row[0], row[1]
        lhs = binom_side(n, j, l, h, b, X)
        rhs = printed_side(n, row, h, b, X)
        if Fraction(lhs) != rhs:
            mismatches.append(((j, l), lhs, rhs, Fraction(rhs, 1) / Fraction(lhs, 1)))
    for (jl, lhs, rhs, ratio) in mismatches:
        if jl == (2, 1) and ratio == 2:
            ratio_ok += 1
    if verbose:
        print(f"n={n}  a,b,c,k,h,s = {a},{b},{c},{k},{h},{s}  (X = {X})")
        print(f"  pairs checked      : {len(PRINTED)}")
        print(f"  pairs mismatching  : {len(mismatches)}")
        for (jl, lhs, rhs, ratio) in mismatches:
            print(f"    (j,l)={jl}: binomial side = {lhs}")
            print(f"               printed  side = {rhs}"
                  f"   -> printed / binomial = {ratio}")
        # total: the whole display, both sides
        tot_l = sum(binom_side(n, r[0], r[1], h, b, X) for r in PRINTED)
        tot_r = sum(printed_side(n, r, h, b, X) for r in PRINTED)
        print(f"  total of the fifteen sums: binomial {tot_l} vs printed {tot_r}"
              f"  (equal: {tot_l == tot_r})")
    return mismatches, ratio_ok


def main() -> int:
    ok = True
    for n in (13, 17, 19):                     # prime n > 11, as the paper assumes
        mm, ratio_ok = screen(n, a=2, b=3, c=5, k=7, h=11)
        if len(mm) != 1 or ratio_ok != 1:
            ok = False
        print()
    print("FINDING REPRODUCED" if ok else "FINDING NOT REPRODUCED - check the screen")
    print("  exactly one printed sum is wrong: (j,l)=(2,1) in the X^3 group,")
    print("  printed without its denominator 2 (2x the binomial value), printed")
    print("  identically at P007-R2 l0 and again at P007-R3 l2.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
