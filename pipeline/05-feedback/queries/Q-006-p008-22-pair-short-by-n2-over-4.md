# Q-006 p. 8's `⇒` X⁴ expansions drop the `n²`-term: the `(2,2)` piece is short by `(n²/4)·Σ i(i−1)…`, the `(3,1)` pair by `(1/6)·Σ i(n³−3n²(i+2))…` [OPEN]

> **Status: OPEN, BLOCKING.** `M1-FRAG-07` (p. 8) can state its first step — the
> congruence modulo `n^{4s+2}` — but stops at the `⇒` rearrangement of the X⁴
> sums, because the expansion of one of them is arithmetically wrong as printed.
> Measured, not inferred: the printed pieces differ from the sum they expand by
> exactly `−(n²/4)·Σ_{i=2}^{n−3} i(i−1) h^{n−3−i} b^{n(i−2)} (n^s abck)^4`.
> The change needed is a single coefficient: the third piece must be
> `+ n(n−1)/4 · Σ i(i−1)…` where the print shows `− n/4 · Σ i(i−1)…`.

## Chunk + PDF ref

- chunk: `pipeline/02-chunks/chunks/M1-FRAG-07.yml` (`BLOCKED`, F4)
- signed region records: `pipeline/01-extract/regions/p007.yml` (R1 l6-l7, the
  source sum), `pipeline/01-extract/regions/p008.yml` (R1 l4-l5, the expansion)
- 300 dpi crop read three times on 2026-09-28:
  `page-008-300dpi-region-01.png` (the coefficient was re-read glyph by glyph:
  the numerator is a **single** `n`, no `(n−1)`, and the sign is a minus)

## What we formalized (plain math)

p. 7 prints the `(j,l) = (2,2)` X⁴ boundary sum as

```
(1/4) * sum_{i=2}^{n-3} (n-1-i)(n-2-i) i(i-1) h^{n-3-i} b^{n(i-2)} (n^s abck)^4
```

p. 8's `⇒` display rewrites the X⁴ group as nine sums, three of which are the
expansion of that one:

| p. 8 R1 | printed piece |
|---|---|
| l4 tail | `− (n/4)  \sum_{i=2}^{n-3} i(i−1) h^{n−3−i} b^{n(i−2)} (n^s abck)^4` |
| l5 | `+ (1/4) \sum_{i=2}^{n-3} (2+i)(1+i) i(i−1) h^{n−3−i} b^{n(i−2)} (n^s abck)^4` |
| l5 | `− (n/2) \sum_{i=2}^{n-3} (1+i) i(i−1) h^{n−3−i} b^{n(i−2)} (n^s abck)^4` |

All three pieces carry the **same range `[2, n−3]`** and the **same**
`h^{n−3−i} b^{n(i−2)} (n^s abck)^4` factor (confirmed twice by vision, and the
ranges explicitly so). Such a decomposition is therefore a **pointwise** identity
in `n` and `i`, and the identity it needs is

```
(n−1−i)(n−2−i) = (i+1)(i+2) − 2n(i+1) + n(n−1),
```

which makes the pieces `(1/4)[(i+2)(i+1) − 2n(i+1) + n(n−1)]·i(i−1)` — i.e. the
third piece must be `+ (n(n−1)/4)·i(i−1)`, not `− (n/4)·i(i−1)`.

## What failed (sympy/exact-arithmetic counterexample, no Lean)

    docker compose exec -T lean python /workspace/pipeline/04-sympy/m1f7_screen.py

exit 0; the relevant section prints (n = 13, h = 11, b = 3, a,b,c,k = 2,3,5,7,
s = 2, X = 35490):

```
  (2,2) pair at n=13: pointwise identity with the printed pieces holds: False
    needed third piece is +(n(n-1)/4)*i(i-1); printed is -(n/4)*i(i-1)
    target-total 2980260271162967406750666291767800075602106629248871693702 /
       (Fraction) ... vs printed-total ...
    gap == -(n^2/4)*sum i(i-1)*h^(n-3-i)*b^(n(i-2))*X^4 : True
```

(the script prints the exact rationals and checks the gap **equals** the
predicted `−(n²/4)Σ i(i−1)·h^{n−3−i}b^{n(i−2)}X⁴`, at n = 13 and n = 17, for two
values of `s`).

## Minimal example

`n = 10`, `i = 2` (no sums, no `h`, no `b`, `X`):

```
target  (n−1−i)(n−2−i)i(i−1)/4 = 7*6*2*1/4            =  21
printed (2+i)(1+i)i(i−1)/4 − (n/2)(1+i)i(i−1) − (n/4)i(i−1)
        = 4*3*2*1/4 − 5*3*2*1 − (10/4)*2*1
        = 6 − 30 − 5                                    = −29
gap     −29 − 21 = −50 = −(n²/4)·i(i−1) = −25*2         ✓
with the corrected third piece:
        6 − 30 + (n(n−1)/4)*i(i−1) = 6 − 30 + (90/4)*2 =  21  ✓
```

## Scope of this claim — what is *not* asserted

Two neighbouring facts from the same screen, recorded so the author can answer
without wondering what we are and are not claiming:

1. **The `(1,3)` expansion is exactly value-preserving pointwise.** Its source
   `−(1/6)(n−1−i)i(i−1)(i−2)` and its two printed pieces
   `+(1/6)(i+1)i(i−1)(i−2) − (n/6)i(i−1)(i−2)` agree for every `i`, because
   `(i+1) − n = −(n−1−i)`. So the frame used for the `(2,2)` claim — same range,
   same `h`/`b`/`X` factors, hence a pointwise identity — is demonstrably the
   frame this display uses.
2. **The same display is short in a SECOND class, measured the same way** — this
   supersedes the earlier "inconclusive" note in this query's first version. The
   `(3,1)` X⁴ pair is expanded on `P007-R2` l7 (= `P008-R1` l3) into
   `+(1/6)·Σ i(i+1)(i+2)(i+3) − (n/6)·Σ i(3i²+12i+11)` over the same range
   `[1, n−4]` with the same `h^{n−4−i} b^{n(i−1)} (n^s abck)^4`, while its source
   on `P007-R1` l5 is `−(1/6)·Σ i(n−1−i)(n−2−i)(n−3−i)`. The identity the pieces
   realise is

   ```
   (n−1−i)(n−2−i)(n−3−i) = n(3i²+12i+11) − (i+1)(i+2)(i+3) + (n³ − 3n²(i+2))
   ```

   and the printed pieces omit the last, `n³/n²`, term. Measured: they are short
   by exactly `(1/6)·Σ_{i=1}^{n−4} i(n³ − 3n²(i+2)) h^{n−4−i} b^{n(i−1)} (n^s abck)^4`,
   i.e. `n²·i·(n − 3i − 6)/6` per term, and restoring that single term returns
   the source exactly (all exact rationals, `n = 13, 17, 19`). No index-shift
   caveat applies here: the pieces carry the source's own range and factors.
   So the `(2,2)` piece and the `(3,1)` pair are **two instances of one
   systematic defect in the same `⇒` display** — expansions that drop the
   `n²`-dependent term.

   The one genuinely *not* checkable that way is none: the `(1,3)` class is
   exactly value-preserving pointwise (`(i+1) − n = −(n−1−i)`), which is the
   control showing that same-range/same-factor pointwise identity is the frame
   this display uses. All of this is in `04-sympy/m1f7_screen.py` (exit 0), whose
   three positive controls reproduce the filed `(2,2)` deficit, the `(3,1)`
   deficit and the `(1,3)` zero-gap.

The `(2,2)` claim itself does not depend on any index convention: it compares the
two printed **sums over the printed range**, in exact rationals, and their
difference is exactly `−(n²/4)·Σ_{i=2}^{n−3} i(i−1) h^{n−3−i} b^{n(i−2)} (n^s abck)^4`.
That is why the minimal instance (`n = 10, i = 2`) can be quoted without sums at
all.

## Question for the author

1. Is the third piece of that expansion
`+ \frac{n(n-1)}{4}\sum_{i=2}^{n-3} i(i-1) h^{n-3-i} b^{n(i-2)} (n^s abck)^4`
— i.e. does the printed `- \frac{n}{4}` lose the factor `(n−1)` and carry the
wrong sign? (With that one coefficient changed, the three printed pieces equal
the p. 7 sum exactly, for every `n` and `i`.)
2. For the `(3,1)` pair on the same display (case 2 of the scope note): is the
missing `(n³ − 3n²(i+2))` term of the expansion omitted deliberately (e.g. it
vanishes modulo `n^{4s+2}` at a later point) or is the printed expansion short?
The same question applies to any other class of this display, since the two
classes found so far both drop exactly the `n²`-dependent term.

## Attachments

- `pipeline/04-sympy/m1f7_screen.py` (exact rationals; exit 0 iff this finding
  and the two structural facts it also records reproduce)
- `pipeline/02-chunks/chunks/M1-FRAG-07.yml` (the blocked chunk, both sides
  transcribed verbatim)
- `pipeline/01-extract/regions/{p007,p008}.yml` (signed) and the crop
  `page-008-300dpi-region-01.png`
- `pipeline/03-lean/M1_LANE.md` §7
