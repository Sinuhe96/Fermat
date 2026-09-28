#!/usr/bin/env python3
"""Triage of defect_sweep groups 5, 6, 7, 8  (throwaway, read-only).

Group 5  P023-R1:l7 P023-R2:l1 P023-R3:l1 P027-R3:l3
Group 6  P023-R2:l0 P023-R3:l0 P025-R1:l0
Group 7  P024-R2:l0 P025-R2:l3 P026-R1:l3
Group 8  P007-R2:l1 P007-R3:l3 P008-R2:l0 P008-R3:l2

Part A  exact integer screen for group 8 (the two X^3 sums printed on the line)
Part B  normalised string diff per group, with the differing tokens printed
Part C  group 5: term multiset of the whole p.23 display, R1 vs R2
"""
from __future__ import annotations
import math
import os
import re
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REGIONS_DIR = os.path.normpath(os.path.join(HERE, "..", "01-extract", "regions"))
DISPLAY = re.compile(r"\\\[(.*?)\\\]", re.S)


def _read_record(page: int):
    """(rid, latex) for every region of pNNN.yml -- line-based, no PyYAML."""
    path = os.path.join(REGIONS_DIR, f"p{page:03d}.yml")
    with open(path, encoding="utf-8") as fh:
        raw = fh.read().splitlines()
    out, rid, i = [], None, 0
    while i < len(raw):
        m = re.match(r"\s*-\s*id:\s*(\S+)", raw[i])
        if m:
            rid = m.group(1).strip()
        if re.match(r"\s*latex:\s*\|", raw[i]):
            i += 1
            block = []
            while i < len(raw) and (raw[i].startswith("      ") or not raw[i].strip()):
                block.append(raw[i][6:])
                i += 1
            out.append((rid, "\n".join(block)))
            continue
        i += 1
    return out


RECS = {}
for _pg in (7, 8, 23, 24, 25, 26, 27):
    for _rid, _latex in _read_record(_pg):
        RECS[(_pg, _rid)] = _latex


def lines(pg, rid):
    return [m.group(1).strip() for m in DISPLAY.finditer(RECS[(pg, rid)])]


GROUPS = {
    5: [("P023", 23, "R1", 7), ("P023", 23, "R2", 1), ("P023", 23, "R3", 1),
        ("P027", 27, "R3", 3)],
    6: [("P023", 23, "R2", 0), ("P023", 23, "R3", 0), ("P025", 25, "R1", 0)],
    7: [("P024", 24, "R2", 0), ("P025", 25, "R2", 3), ("P026", 26, "R1", 3)],
    8: [("P007", 7, "R2", 1), ("P007", 7, "R3", 3), ("P008", 8, "R2", 0),
        ("P008", 8, "R3", 2)],
}

IGNORE_LITERALS = ["\\Rightarrow", "\\left", "\\right", "\\,", "{", "}"]
IGNORE_PATTERNS = [r"\\textcolor\{[a-z]+\}\{?", r"\\text\{[^}]*\}",
                   r"\\mathbf\{", r"\\;"]


def strip_ignorable(s: str) -> str:
    for pat in IGNORE_PATTERNS:
        s = re.sub(pat, "", s)
    for lit in IGNORE_LITERALS:
        s = s.replace(lit, "")
    return re.sub(r"\s+", " ", s).strip()


def word_tokens(s: str):
    return re.findall(r"\\[A-Za-z]+|[A-Za-z]+|\d+|[^\s]", strip_ignorable(s))


# ---------------------------------------------------------------- Part A
def X_of(n, a, b, c, k, s):
    return n ** s * a * b * c * k


def printed(l, sgn, lo, hi, coef, hpow, bpow, n, h, b, X, xpow):
    tot = Fraction(0)
    for i in range(lo, hi + 1):
        tot += coef(i) * h ** hpow(i) * b ** bpow(i) * X ** xpow
    return sgn * tot


def binom_side(j, l, n, h, b, X):
    """(-1)^j C(n-1-i, j) C(i, l) h^{n-1-i-j} b^{n(i-l)} X^{j+l}, i in [l, n-1-j]."""
    tot = 0
    for i in range(l, n - j):
        if n - 1 - i < j or i < l:
            continue
        tot += (-1) ** j * math.comb(n - 1 - i, j) * math.comb(i, l) \
            * h ** (n - 1 - i - j) * b ** (n * (i - l)) * X ** (j + l)
    return tot


def part_a():
    print("=" * 78)
    print("PART A  group 8: exact integer screen of the two X^3 sums on the line")
    print("=" * 78)
    for (n, h, b, a, c, k, s) in [(13, 11, 3, 2, 5, 7, 1), (17, 11, 3, 2, 5, 7, 1)]:
        X = X_of(n, a, b, c, k, s)
        print(f"\nn={n}  h={h} b={b} a={a} c={c} k={k} s={s}  (X = {X})")

        # (j,l)=(3,0):  printed  -1/6 sum_{i=0}^{n-4}(n-1-i)(n-2-i)(n-3-i) h^{n-4-i} b^{ni} X^3
        p30 = printed(None, -1, 0, n - 4,
                      lambda i: Fraction((n - 1 - i) * (n - 2 - i) * (n - 3 - i), 6),
                      lambda i: n - 4 - i, lambda i: n * i, n, h, b, X, 3)
        b30 = binom_side(3, 0, n, h, b, X)
        # (j,l)=(0,3):  printed  +1/6 sum_{i=3}^{n-1} i(i-1)(i-2) h^{n-1-i} b^{n(i-3)} X^3
        p03 = printed(None, +1, 3, n - 1,
                      lambda i: Fraction(i * (i - 1) * (i - 2), 6),
                      lambda i: n - 1 - i, lambda i: n * (i - 3), n, h, b, X, 3)
        b03 = binom_side(0, 3, n, h, b, X)
        print(f"  (j,l)=(3,0) printed  : {p30}")
        print(f"  (j,l)=(3,0) binomial : {b30}   equal: {p30 == b30}")
        print(f"  (j,l)=(0,3) printed  : {p03}")
        print(f"  (j,l)=(0,3) binomial : {b03}   equal: {p03 == b03}")
        # contrast: the (2,1) sum which is Q-005 (NOT on this line)
        p21 = printed(None, +1, 1, n - 3,
                      lambda i: i * (n - 1 - i) * (n - 2 - i),
                      lambda i: n - 3 - i, lambda i: n * (i - 1), n, h, b, X, 3)
        b21 = binom_side(2, 1, n, h, b, X)
        print(f"  (j,l)=(2,1) printed  : {p21}")
        print(f"  (j,l)=(2,1) binomial : {b21}   equal: {p21 == b21}  "
              f"(ratio {Fraction(p21, b21)})  <- Q-005, different line")
        # min instance of (3,0)/(0,3)
        n_, i_ = n, 1
        lhs30 = Fraction((n_ - 1 - i_) * (n_ - 2 - i_) * (n_ - 3 - i_), 6)
        print(f"  min instance (3,0) n={n_}, i={i_}: C(n-1-i,3)={math.comb(n_-1-i_,3)} "
              f" vs printed/1 * ... = {lhs30}   equal: {lhs30 == math.comb(n_-1-i_,3)}")


# ---------------------------------------------------------------- Part B
def part_b():
    print()
    print("=" * 78)
    print("PART B  normalised token diff per group")
    print("=" * 78)
    for g, sites in GROUPS.items():
        print(f"\n--- group {g} ---")
        forms = []
        for (pp, pg, rid, k) in sites:
            ln = lines(pg, rid)[k]
            forms.append(((f"{pp}-{rid}:l{k}"), strip_ignorable(ln)))
        for name, f in forms:
            print(f"  {name:16s} {f}")
        # pairwise token diff vs first
        base_name, base = forms[0]
        for name, f in forms[1:]:
            a, b = word_tokens(base), word_tokens(f)
            na, nb = [], []
            for t in a:
                if t in b:
                    b.remove(t)
                else:
                    na.append(t)
            nb = b
            print(f"  tokens in {base_name} not in {name}: {na}")
            print(f"  tokens in {name} not in {base_name}: {nb}")


# ---------------------------------------------------------------- Part C
def split_terms(s):
    s = strip_terms_safe(s)
    terms, depth, cur = [], 0, ""
    for idx, ch in enumerate(s):
        if ch in "{([":
            depth += 1
        elif ch in "})]":
            depth -= 1
        if ch in "+-" and depth == 0 and cur.strip():
            terms.append(cur.strip())
            cur = ch
        else:
            cur += ch
    if cur.strip():
        terms.append(cur.strip())
    return [t for t in terms if t.strip(" +-\t")]


def strip_terms_safe(s: str) -> str:
    """Brace-preserving: drop colour/prose/left-right/spacing only."""
    s = re.sub(r"\\textcolor\{[a-z]+\}\{?", "", s)
    s = re.sub(r"\\text\{[^}]*\}", "", s)
    for lit in ["\\left", "\\right", "\\,", "\\;", "\\!", "\\qquad", "\\quad"]:
        s = s.replace(lit, "")
    return re.sub(r"\s+", "", s)


def seg_after_last_eq(joined: str):
    """The terms printed after the LAST top-level '=' of a chain display."""
    s = strip_terms_safe(joined)
    depth, last = 0, -1
    for idx, ch in enumerate(s):
        if ch in "{([":
            depth += 1
        elif ch in "})]":
            depth -= 1
        elif ch == "=" and depth == 0:
            last = idx
    return split_terms(s[last + 1:])


def part_c():
    print()
    print("=" * 78)
    print("PART C  group 5: term multiset of the whole p.23 display, R1 vs R2")
    print("=" * 78)
    r1 = " ".join(lines(23, "R1")[6:9])       # R1 l6+l7+l8: the "Ta có: Q = A = B" chain
    r2 = " ".join(lines(23, "R2")[:7])        # R2 l0..l6: the "= C" chain
    t1 = seg_after_last_eq(r1)                # R1's expansion B
    t2 = seg_after_last_eq(r2)                # R2's expansion C
    print(f"R1 expansion (B), {len(t1)} terms:")
    for t in t1:
        print("   ", t)
    print(f"R2 expansion (C), {len(t2)} terms:")
    for t in t2:
        print("   ", t)
    rem = list(t2)
    miss = []
    for t in t1:
        if t in rem:
            rem.remove(t)
        else:
            miss.append(t)
    print("\nR1 expansion terms NOT printed verbatim in R2's expansion:")
    for t in miss:
        print("   ", t)
    rem = list(t1)
    extra = []
    for t in t2:
        if t in rem:
            rem.remove(t)
        else:
            extra.append(t)
    print("R2 expansion terms NOT printed verbatim in R1's expansion:")
    for t in extra:
        print("   ", t)
    for key in ["hb^{n(n-3)}", "a^{n(n-4)}", "M_1", "C_3", "B_3"]:
        print(f"\n'{key}' occurrences:  R1 l6-l8 = {r1.count(key)},  R2 l0-l6 = {r2.count(key)}")


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
