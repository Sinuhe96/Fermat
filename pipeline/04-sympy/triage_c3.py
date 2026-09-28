"""Triage check: the auxiliary quantity `C_3` as printed at `P014-R1` and again
at `P023-R1` (main proof, pp. 14 and 23).

Both regions print `C_3` multiplied by the same remaining factor
`(2 n^s abck) / (h - b^n)^3`, so the two printed bracket-groups must be equal as
polynomials in `b, h` (n is a fixed prime). They are not:

  P014-R1  5n[h^{n-2} - b^{n(n-2)}] + 2n b^n h[h^{n-4} - b^{n(n-4)}]
  P023-R1  [-5n h^{n-2} + 2n b^n h^{n-3}] + [5n b^{n(n-2)} - 2n h b^{n(n-3)}]

The second and fourth monomials agree once the printed spellings are normalised
(`b^n h^{n-3} = h^{n-3} b^n`, and `b^n h b^{n(n-4)} = h b^{n(n-3)}`); the first
and third carry opposite signs. This script measures the residual exactly, and
checks the second group (the one over `(h - b^n)^2`), so the finding is a number
rather than a reading.

Run in the container:
    docker compose exec -T lean python /workspace/pipeline/04-sympy/triage_c3.py
"""
import sympy as sp

b, h = sp.symbols("b h", positive=True)


def group3_p014(n):
    """P014-R1: the bracket multiplying (2 n^s abck)/(h - b^n)^3."""
    return 5 * n * (h ** (n - 2) - b ** (n * (n - 2))) + 2 * n * b**n * h * (
        h ** (n - 4) - b ** (n * (n - 4))
    )


def group3_p023(n):
    """P023-R1: the numerator multiplying (2 n^s abck)/(h - b^n)^3."""
    return (-5 * n * h ** (n - 2) + 2 * n * b**n * h ** (n - 3)) + (
        5 * n * b ** (n * (n - 2)) - 2 * n * h * b ** (n * (n - 3))
    )


def group2_p014(n):
    """P014-R1: the group over (h - b^n)^2."""
    return n**3 * b**n * h * (h ** (n - 4) - b ** (n * (n - 4))) - n**3 * (
        h ** (n - 2) - b ** (n * (n - 2))
    )


def group2_p023(n):
    """P023-R1: the two groups over (h - b^n)^2 (signs as printed)."""
    return -(n**3 * h ** (n - 2) - n**3 * b**n * h ** (n - 3)) + (
        n**3 * b ** (n * (n - 2)) - n**3 * h * b ** (n * (n - 3))
    )


def seven_p023_num(n):
    """P023-R2's numerator, written in (h - b^n) normal form."""
    hb = h - b**n
    return (
        -7 * b ** (n * (n - 4)) * hb**3
        + 7 * b ** (n * (n - 3)) * hb**2
        - 7 * b ** (n * (n - 2)) * hb
        + h ** (n - 1)
        - b ** (n * (n - 1))
    )


def seven_p024_num(n):
    """P024-R1's numerator: minus the verified bracket, so +7 distributes over
    all three terms of `-7b^(n(n-4)) + 7b^(n(n-3)) - 7[b^(n(n-2)) + h^(n-1) - b^(n(n-1))]`."""
    hb = h - b**n
    return (
        7 * b ** (n * (n - 4)) * hb**3
        - 7 * b ** (n * (n - 3)) * hb**2
        + 7 * b ** (n * (n - 2)) * hb
        + 7 * h ** (n - 1)
        - 7 * b ** (n * (n - 1))
    )


def c3_three_way(n):
    """The bracket as printed at P023-R1, P023-R2 and P024-R1 (identical text)."""
    return (-5 * n * h ** (n - 2) + 2 * n * b**n * h ** (n - 3)) + (
        5 * n * b ** (n * (n - 2)) - 2 * n * h * b ** (n * (n - 3))
    )


def main() -> int:
    print("== group over (h - b^n)^3, times (2 n^s abck) ==")
    bad = 0
    for n in (13, 17, 19):
        d = sp.expand(group3_p014(n) - group3_p023(n))
        predicted = sp.expand(10 * n * (h ** (n - 2) - b ** (n * (n - 2))))
        same = sp.simplify(d - predicted) == 0
        print(f"  n={n:<3} P014-P023 = {sp.factor(d)}   matches 10n(h^(n-2)-b^(n(n-2))): {same}")
        if not same:
            bad += 1
    print("== group over (h - b^n)^2 ==")
    for n in (13, 17, 19):
        d = sp.expand(group2_p014(n) - group2_p023(n))
        print(f"  n={n:<3} P014-P023 = {d}   identical: {d == 0}")
        if d != 0:
            bad += 1
    print()
    print("== the `7...` numerator over (h - b^n)^4: P023-R2 vs P024-R1 ==")
    for n in (13, 17, 19):
        d = sp.expand(seven_p023_num(n) - seven_p024_num(n))
        # The finding is that the two prints DISAGREE; the closed form of the
        # difference is reported, not predicted. (A first version of this check
        # asserted `8(h^(n-1) - b^(n(n-1)))` and was falsified by it — the
        # difference is not that, so the check now tests non-vanishing only.)
        print(f"  n={n:<3} difference is non-zero: {d != 0}")
        print(f"        factored: {sp.factor(d)}")
        if d == 0:
            bad += 1
    print("  reading: P023-R2 prints `... - 7b^(n(n-2))(h-b^n) + h^(n-1) - b^(n(n-1))`,")
    print("  i.e. the printed 7 does not reach the last two summands, while P024-R1")
    print("  writes them inside the bracket `-7[... + h^(n-1) - b^(n(n-1))]`. The")
    print("  two printed numerators differ by the non-zero polynomial above, so the")
    print("  readings are genuinely different statements — same class as the C_3")
    print("  finding (a printed factor that fails to distribute over a bracket).")
    print()
    print("== C_3 three-way: the bracket text is identical at P023-R1, P023-R2, P024-R1 ==")
    print("  so P014-R1 is the single outlier of four prints that name C_3.")
    print()
    print("reading: the (h-b^n)^2 groups agree exactly, so the printed spellings")
    print("normalise as expected; the (h-b^n)^3 numerator differs by a non-zero")
    print("polynomial, and the difference is NOT a global sign flip (the two terms")
    print("2n b^n h^(n-3) and -2n h b^(n(n-3)) are common to both prints).")
    print("=> one of the two regions misprints two signs; the p.14 / p.23 leaves")
    print("   cannot both be stated as printed.")
    # EXIT 0 == the discrepancy is exactly as predicted above (repo convention:
    # this script is a finding-reproduction, not a pass/fail of the author).
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
