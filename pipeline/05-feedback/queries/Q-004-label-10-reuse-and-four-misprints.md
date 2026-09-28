# Q-004 Label (10) reused on p. 27, and four printed factors that miss part of their bracket [OPEN]

> **Status: OPEN, not blocking.** Two classes of *print* defect in the pp. 14–27
> expansion stretch. Item 1 is a documentation defect (a result is reachable only
> through a double-meaning label); items 2.1–2.4 are all one failure mode — a
> printed factor that reaches some summands of its bracketed group and not others
> — where four different regions disagree with each other. Each item records the
> **measured** difference. No chunk is blocked: the Lean lane is at p. 10, and
> each item is filed with the measurement so the author can answer in one line.
> All four items reproduce without Lean (commands below).

## Chunk + PDF ref

- signed region records: `pipeline/01-extract/regions/p006.yml`,
  `p014.yml`, `p022.yml`, `p023.yml`, `p024.yml`, `p025.yml`, `p026.yml`,
  `p027.yml`
- 300 dpi crops read: `page-016-…-02.png`, `page-023-…-02.png`,
  `page-025-…-01.png`, `page-026-…-02.png`

## Item 1 — the number `(10)` is used twice, for different results

`(10)` is printed on p. 6 R2 as the `n^{5s+1}` display. It is printed **again**
on p. 27 R3 carrying the content of p. 6's **`(7)`**:

```
h^n − a^{n^2} − b^{n^2} ≡ n[a^{n(n−1)} + b^{n(n−1)} + h^{n−1}] n^s abck (mod n^{2s+1})
```

so two different results both answer to `(10)`. The number is *cited* later
(p. 18 R2: "Từ (10), (9), (8), (7) và (13) suy ra"), which makes the double
meaning a real ambiguity for any reader — and for us it is a hazard, since the
p. 27 leaf would otherwise inherit p. 6's `(7)` under the wrong label.

**Suggestion.** Re-number the p. 27 R3 line (e.g. `(10′)`) or reprint it as `(7)`.

## Item 2 — one failure mode, four sites: a factor that misses part of its group

### 2.1 — `C₃` signs, p. 14 R1 vs its three re-prints

The same quantity is printed four times. `P014-R1` differs from the other three
(`P023-R1`, `P023-R2`, `P024-R1`, which agree with each other) by exactly

```
10 n (h^{n−2} − b^{n(n−2)})
```

measured; and the companion `(h−b^n)^2` groups are **identical** between p. 14
and p. 23 (difference 0), which rules out a denominator convention as the
explanation. So p. 14 is the outlier of four.

### 2.2 — the `7…` numerator over `(h−b^n)^4`

`P023-R2` and `P024-R1` print this numerator differently; the difference is a
non-zero polynomial. **Note on our own evidence:** our first hand-derived closed
form for that difference (`8(h^{n−1} − b^{n(n−1)})`) was **falsified** by the
check script, so no closed form is claimed here — only the measured non-zero
difference and the two quoted lines.

### 2.3 — the magenta coefficient: `2n(n−1)` vs `2(n−1)`

The same term, same colour, same bracket, same denominator, in three prints:

| region | printed coefficient |
|---|---|
| `P022-R3` | `2n(n−1)` |
| `P025-R1` | `2n(n−1)` |
| `P026-R2` | `2(n−1)` |

i.e. p. 26 is the minority reading, differing by exactly a factor `n`. (Caveat we
do not hide: the `P022-R3` and `P025-R1` prints are both "T ≡ …" assemblies of
the same quantity, so they may not be independent evidence — the count is
suggestive, not decisive.)

### 2.4 — a dropped factor `n` on one summand, p. 22 R2

p. 22 R2 prints

```
[ n(2h^{n−3}a^n(−2n^s abck) − 2b^{n(n−3)}a^n(2n^s abck)) − 18b^{n(n−2)}(2n^s abck) ] / (6(h−b^n)^3) · (n^s abck)^3
```

and its own next line, one line below, prints the same term as

```
− (2nh^{n−3}a^n + 2nb^{n(n−3)}a^n + 18n b^{n(n−2)}) / (3(h−b^n)^3) · (n^s abck)^4
```

The outer `n(…)` in the first line reaches only the first two summands: the
`18b^{n(n−2)}` term sits **outside** it, while the line below writes
`18n b^{n(n−2)}`. Everything else agrees (÷6·(n^s abck)^3 with a `2n^s abck`
inside = ÷3·(n^s abck)^4). This is the same failure mode as 2.1–2.3, one line
apart, which is what makes the class look systematic rather than random.

## Reproduction (no Lean)

    python pipeline/04-sympy/triage_c3.py        # items 2.1 and 2.2, exit 0
    python pipeline/01-extract/cite_index.py     # item 1 (reports (10) as REUSED)
    python pipeline/04-sympy/m1_common.py        # the lane's vacuity/expansion screen

`triage_c3.py` measures each printed pair by symbolic difference and prints the
difference; it is the same measurement procedure that **falsified our own first
hand-derived formula** for item 2.2, which is why every claim above is stated as
"measured difference" rather than as a repaired formula.

## Question for the author

1. For each of 2.1–2.4: which of the two printed readings is intended? (In 2.1
   and 2.3 the majority reading is the one we would encode; in 2.2 and 2.4 the
   two readings are one line apart and we will not choose without you.)
2. Is the repeated `(10)` on p. 27 R3 meant to be a new number?

## Attachments

- `pipeline/04-sympy/triage_c3.py`, `pipeline/04-sympy/m1_common.py`
- `pipeline/01-extract/cite_index.py`, `pipeline/01-extract/out/citations.tsv`
- the eight signed region records listed above; the four crops listed above
- `pipeline/03-lean/M1_LANE.md` §7 — the triage table with each measurement
