#!/usr/bin/env python3
"""sweep_constants.py -- exact-rational sweep for printed constants that
contradict their own local computation (pp. 9-33 of PROOF_of_FERMAT.pdf).

Pure `fractions` arithmetic; no floats, no SymPy.
Monomials  a^{p(n)} b^{q(n)} c^{r(n)} h^{s(n)}  are represented by the tuple of
exponent polynomials in n (each polynomial = tuple of int coefficients, low
order first), so all bookkeeping is exact.  A "CONTRADICTION" line is a place
where a printed constant differs from its own printed local computation.

Run:  MSYS_NO_PATHCONV=1 docker compose exec -T lean \
        python /workspace/pipeline/04-sympy/sweep_constants.py
"""
from fractions import Fraction as F

CONTRADICTIONS = []


def poly(*cs):
    cs = list(cs)
    while len(cs) > 1 and cs[-1] == 0:
        cs.pop()
    return tuple(cs)


def padd(*ps):
    out = [0] * max(len(p) for p in ps)
    for p in ps:
        for i, c in enumerate(p):
            out[i] += c
    return poly(*out)


def pstr(p):
    return "+".join(f"{c}n^{i}" if i else f"{c}" for i, c in enumerate(p) if c)


def nn(k):
    """exponent polynomial n*(n-k)"""
    return poly(0, -k, 1)


def nk(k):
    """exponent polynomial k*n"""
    return poly(0, k)


def c0():
    return poly(0)


# monomials: (a-exponent, b-exponent, c-exponent, h-exponent)
A_ = (nn(2), c0(), c0(), c0())        # a^{n(n-2)}
B_ = (c0(), nn(2), c0(), c0())        # b^{n(n-2)}
H_ = (c0(), c0(), c0(), poly(-2, 1))  # h^{n-2}
X_ = (nn(1), c0(), c0(), c0())        # a^{n(n-1)}
Y_ = (nk(1), nn(2), c0(), c0())       # a^n b^{n(n-2)}
Z_ = (nk(2), nn(3), c0(), c0())       # a^{2n} b^{n(n-3)}
W_ = (nn(2), c0(), nk(1), c0())       # a^{n(n-2)} c^n
T_ = (nk(1), c0(), nn(2), c0())       # a^n c^{n(n-2)}
bna = (nk(1), nn(3), c0(), c0())      # a^n b^{n(n-3)}
bnh3 = (c0(), poly(1), c0(), poly(-3, 1))   # b^n h^{n-3}
anh3 = (poly(1), c0(), c0(), poly(-3, 1))   # h^{n-3} a^n
hb = (c0(), nn(3), c0(), poly(1))     # h b^{n(n-3)}


def collect(terms):
    acc = {}
    for c, m in terms:
        acc[m] = acc.get(m, F(0)) + F(c)
    return {m: c for m, c in acc.items() if c != 0}


def show(d):
    if not d:
        return "0"

    def mono(m):
        return "".join(f"{s}^{{{pstr(e)}}}" if e != (0,) else ""
                       for s, e in zip("abch", m))
    return "  ".join(f"{'+' if c > 0 else '-'}{abs(c)}*{mono(m)}"
                     for m, c in sorted(d.items(), key=str))


def check(tag, printed, computed, expect_match=True):
    """expect_match=False marks a designed contradiction."""
    ok = (printed == computed) == expect_match
    label = ("OK " if ok else "BAD") if expect_match else \
            ("CONTRADICTION" if ok else "unexpected-ok")
    print(f"[{label}] {tag}: printed={printed} computed={computed}")
    if expect_match and not ok:
        print("        ^ UNEXPECTED")
    if (not expect_match) and ok:
        CONTRADICTIONS.append(tag)


print("=" * 78)
print("C1  P033-R1 (p.33): the 14-term  b^{n(n-1)}  assembly -> printed 55/3")
print("=" * 78)
c33 = [F(4), F(-65, 4), F(4, 3), F(4), F(1, 4), F(-15, 2), F(28), F(-15),
       F(1, 4), F(2), F(16, 3), F(-7), F(-5, 3), F(16)]
total = sum(c33, F(0))
print(f"   14 printed coefficients sum to {total} ({total.numerator}/{total.denominator})")
check("P033-R1 penultimate-line sum", F(55, 4), total)
check("P033-R1 final line 55/3", F(55, 3), total, expect_match=False)

grouped = [                                    # (coeff, b-exponent polynomial)
    (F(4), nn(1)),                                  # 4 b^{n(n-1)}
    (F(5, 4) * 3 * -1, padd(nn(4), nk(3))),         # 5[3 b^{n(n-4)}(-b^{3n})]/4
    (F(5, 4) * -4, padd(nn(3), nk(2))),             # 5[-4 b^{n(n-3)}b^{2n}]/4
    (F(5, 4) * 6 * -1, padd(nn(2), nk(1))),         # 5[6 b^{n(n-2)}(-b^n)]/4
    (F(4, 3), padd(nn(3), nk(2))),                  # +4 b^{n(n-3)}b^{2n}/3
    (F(-15), padd(nn(3), nk(2))),                   # -15 b^{n(n-3)}b^{2n}
    (F(4), padd(nn(2), nk(1))),                     # 4(-b^{n(n-2)})(-b^n)
    (F(1, 4), padd(nn(4), nk(3))),                  # (-b^{n(n-4)})(-b^n)^3/4
    (F(9 * -1 - 6, 2), padd(nn(3), nk(2))),         # [9(-1)-6]/2
    (F(1, 4), padd(nn(5), nk(4))),                  # b^{n(n-5)}b^{4n}/4
    (F(-7 * -1 + 7 - 7 * (-1 - 1)), nn(1)),         # -7(-1)+7-7(-2) = 28
    (F(-7), padd(nn(2), nk(1))),                    # 7 b^{n(n-2)}(-b^n)
    (F(-5, 3), padd(nn(2), nk(1))),                 # 5 b^{n(n-2)}(-b^n)/3
    (F(2), padd(nn(3), nk(2))),                     # +2 b^{n(n-3)}b^{2n}
    (F(-(2 - 18), 3), padd(nn(3), nk(2))),          # -(2-18)/3
    (F(16), padd(nn(3), nk(2))),                    # 8[..+..]b^{2n} = 16
]
allsame = all(e == nn(1) for _, e in grouped)
print("   every grouped term's b-exponent equals n(n-1)? "
      f"{allsame}   (n(n-1) = {pstr(nn(1))})")
gs = sum((c for c, _ in grouped), F(0))
print(f"   grouped-display coefficient sum = {gs}")
check("P033-R1 grouped-display coefficient", F(55, 4), gs)

print()
print("=" * 78)
print("C2  P031-R2 (p.31): collection of the (n^s abck)^1 list (crop-confirmed)")
print("=" * 78)
terms31 = [
    (F(6), Y_), (F(-1), X_),                        # +[6Y - X]
    (F(2, 3), X_), (F(-6), Y_),                     # -(-2X+18Y)/3
    (F(-4, 3), X_), (F(2, 3), W_),                  # -(4X-2W)/3
    (F(15, 4), X_), (F(-5), Z_), (F(15, 2), Y_),    # +5[3X-4Z+6Y]/4
    (F(1, 4), X_), (F(-1, 3), Z_), (F(-1, 2), T_),  # -(-3X+4Z+6T)/12
    (F(-3), X_),                                    # (-5X-4X)/3
    (F(-1), X_),                                    # -X
    (F(-7), X_), (F(7), Z_), (F(-7), Y_),           # [-7X+7Z-7Y]
    (F(3), X_), (F(-3), Z_),                        # (9X-3[2Z+X])/2
    (F(-15), X_), (F(-3, 4), X_), (F(2), X_), (F(-4), X_), (F(1, 4), X_), (F(24), X_),
]
c31 = collect(terms31)
printed31 = collect([(F(2, 3), W_), (F(-2, 3), Z_), (F(5, 6), X_)])
print(f"   collected from the list : {show(c31)}")
print(f"   printed next line       : {show(printed31)}")
check("P031-R2  X=a^{n(n-1)}", F(5, 6), c31.get(X_, F(0)))
check("P031-R2  W=c^n a^{n(n-2)}", F(2, 3), c31.get(W_, F(0)))
check("P031-R2  Z=b^{n(n-3)}a^{2n}", F(-2, 3), c31.get(Z_, F(0)), expect_match=False)
check("P031-R2  Y=b^{n(n-2)}a^n (printed: absent)", F(0), c31.get(Y_, F(0)),
      expect_match=False)
check("P031-R2  T=c^{n(n-2)}a^n (printed: absent)", F(0), c31.get(T_, F(0)),
      expect_match=False)
check("P031-R2  collected == printed", printed31, c31, expect_match=False)
check("P031-R2  (23): 2/3 + 5/6", F(3, 2), F(2, 3) + F(5, 6))

print()
print("=" * 78)
print("C3  P029-R3/P030-R1 (pp.29-30): sign of the b^{n(n-3)}(h-a^n) term")
print("=" * 78)
# P029-R3 line 3 bracket: -3[A+B-h] + b^{n(n-3)}(h-a^n) - h^{n-3}(a^n+b^n) + a^{n(n-2)}
# expanded with h-a^n -> b^n+2K, a^n+b^n -> h-2K and every 2K term dropped
# (each carries an extra n^s; the whole bracket is multiplied by n):
line3 = collect([
    (F(-3), A_), (F(-3), B_), (F(3), H_),   # -3[A + B - h]
    (F(1), bna), (F(1), B_),                # +b^{n(n-3)}(h-a^n) = +b^{n(n-3)}a^n + B_
    (F(-1), bna),                           # -b^{n(n-3)}a^n
    (F(-1), H_),                            # -h^{n-3}(a^n+b^n) -> -h^{n-2}
    (F(1), A_),                             # +a^{n(n-3)}a^n = A_
])
corrected = collect([(F(-2), A_), (F(-2), B_), (F(2), H_)])
check("P029-R3 line 3 reduces to", corrected, line3)
# P030-R1 line 4 as printed: the b^{n(n-3)}(h-a^n) term carries the OPPOSITE sign
line4 = collect([
    (F(-3), A_), (F(-3), B_), (F(3), H_),
    (F(-1), B_), (F(-1), H_), (F(1), A_),   # -b^{n(n-2)} - h^{n-2} + a^{n(n-2)}
])
check("P030-R1 line 4 bracket (printed)", corrected, line4, expect_match=False)
# P030-R1 line 6 as printed (the n/2 prefactor of line 4 becomes n):
line6 = collect([(F(-1), A_), (F(-1), B_), (F(1), H_)])
check("P030-R1 line 6 numerator (printed)", corrected,
      {m: 2 * c for m, c in line6.items()})
check("P030-R1 line 4/2 == line 6", line6, {m: c / 2 for m, c in line4.items()},
      expect_match=False)
# independent: the P029-R1 definition of H(h,b), same expansion
definition = collect([
    (F(-3), A_), (F(-3), B_), (F(3), H_),
    (F(1), bna), (F(1), B_),                # +b^n h b^{n(n-4)} = b^{n(n-3)}h
    (F(-1), bnh3), (F(-1), anh3),           # -b^n h^{n-3} - h^{n-3} a^n
    (F(-1), bna),                           # -b^{n(n-3)} a^n
    (F(1), A_),                             # +a^{n(n-3)}a^n
])
cb = definition.pop(bnh3, F(0))
ca = definition.pop(anh3, F(0))
assert cb == ca, "the two h^{n-3} pieces must share a coefficient"
definition[H_] = definition.get(H_, F(0)) + cb   # (a^n+b^n)h^{n-3} -> h^{n-2}
definition = {m: c for m, c in definition.items() if c != 0}
print(f"   P029-R1 definition reduces to : {show(definition)}")
check("P029-R1 definition reduction", corrected, definition)

print()
print("=" * 78)
print("C4  P009-R2/P010-R1 (pp.9-10): the M coefficient sums")
print("=" * 78)
mF = F(1, 24) + F(1, 6) + F(1, 6) + F(1, 4)
check("P010-R1 15/24", F(15, 24), mF)
check("P010-R1 1/24", F(1, 24), F(1, 24))
check("P010-R1 -7n/6", F(-7, 6), -(F(1, 2) + F(1, 6) + F(1, 2)))
check("P010-R1 -3n/4", F(-3, 4), -(F(1, 2) + F(1, 4)))
check("P010-R1 -n/3", F(-1, 3), -F(1, 3))
check("P011-R2 'M = 16(...)': 15/24+1/24", F(16, 24), mF + F(1, 24))

print()
print("=" * 78)
print("C5  P014-R1 D / P020-R3 (15) / P023-R1 Q  -- consistency re-checks")
print("=" * 78)
check("P014-R1 D: 1+1+2 -> 4", F(4), F(1) + F(1) + F(2))
# P020-R2: numerator of the  /2(h-b^n)^2  line, /2, must equal the next line's
# numerator over (h-b^n)^2
bN1 = (c0(), nn(1), c0(), c0())          # b^{n(n-1)}
hN1 = (c0(), c0(), c0(), poly(-1, 1))    # h^{n-1}
aY = (nk(1), nn(2), c0(), c0())          # a^n b^{n(n-2)}
aH = (nk(1), c0(), c0(), poly(-2, 1))    # a^n h^{n-2}
bH = (c0(), nn(2), c0(), poly(1))        # b^{n(n-2)} h
Hb = (c0(), poly(1), c0(), poly(-2, 1))  # h^{n-2} b^n
N1 = collect([
    (F(-1), aY), (F(-1), X_), (F(1), aH),                     # -[B+A-h]a^n
    (F(4), X_), (F(4), bN1), (F(4), hN1),                     # +4[X+B'+h^{n-1}]
    (F(-2), bH), (F(-2), bN1), (F(-2), Hb), (F(-2), hN1),     # -[2b^{n(n-2)}h+...]
    (F(-3), aH), (F(3), aY), (F(-3), X_),                     # -3[h^{n-2}-b^{n(n-2)}]a^n
])
N2 = collect([(F(1), bN1), (F(1), aY), (F(-1), bH), (F(-1), aH),
              (F(-1), Hb), (F(1), hN1)])
print(f"   P020-R2 numerator/2 = {show({m: c/2 for m, c in N1.items()})}")
print(f"   P020-R2 next line   = {show(N2)}")
check("P020-R2 numerator/2 == next line", N2, {m: c / 2 for m, c in N1.items()})
p15 = collect([(F(-2), B_), (F(2), H_), (F(-3), H_), (F(3), B_)])
check("P020-R3 (15): b^{n(n-2)} - h^{n-2}", collect([(F(1), B_), (F(-1), H_)]), p15)
B2 = [(F(2), B_), (F(-2), hb), (F(-3), B_), (F(2), hb), (F(1), H_)]
C2 = [(F(6), H_), (F(-3), bnh3), (F(3), hb), (F(-6), B_)]
lhs = collect([(F(1, 2) * c, m) for c, m in B2] + [(F(1, 6) * c, m) for c, m in C2])
# the pieces P023-R1 itself prints on the right of  Q = Q_1 + M_1 X^4 + 1/2 B_3 X^3 + 1/6 C_3 X^3
printed_q = collect([
    (F(1, 2) * F(-3), B_), (F(1, 2) * F(2), hb), (F(1, 2) * F(1), H_),   # 1/2 of B_2
    (F(1), B_), (F(-1), hb),                                            # its first two pieces
    (F(1, 2) * F(2), H_), (F(1, 2) * F(-1), bnh3),
    (F(1, 2) * F(1), hb), (F(1, 2) * F(-2), B_),                        # 1/6 of C_2
])
print(f"   1/2 B_2 + 1/6 C_2      = {show(lhs)}")
print(f"   P023-R1 printed pieces = {show(printed_q)}")
check("P023-R1  1/2 B_2 + 1/6 C_2", lhs, printed_q)

print()
print("=" * 78)
print("C6  P009-R2 (p.9): the 'Quy uoc' denominator list")
print("=" * 78)
printed_m = {1, 2, 3, 4, 6, 12}
# denominators m that the paper goes on to use: 1/m coefficients (2,3,4,6,12,24)
# and the explicit m(h-b^n) denominators (24(h-b^n) on pp.22 R3, 24 R1, 27 R1)
used_after = {1, 2, 3, 4, 6, 12, 24}
print(f"   printed m-list               : {sorted(printed_m)}")
print(f"   24 occurs as a denominator?  : {24 in used_after}"
      f"   (M = 1/24*sum on p.9 R2 itself; 24(h-b^n) on pp.22,24,27)")
check("p.9 Quy uoc m-list is complete", used_after, printed_m, expect_match=False)
print(f"   denominators used but absent from the printed list: "
      f"{sorted(used_after - printed_m)}")

print()
print("=" * 78)
print("FINDINGS (printed constant contradicts its own local computation):")
for t in CONTRADICTIONS:
    print("  *", t)
if not CONTRADICTIONS:
    print("  (none)")
print("=" * 78)
