# Q-005 p. 7 prints the `(j,l) = (2,1)` sum of the `(n^s abck)^3` group without its denominator 2 [OPEN]

> **Status: OPEN, BLOCKING.** `M1-FRAG-05` (and therefore `M1-FRAG-06`, whose
> display continues the same line) is `BLOCKED` on this question. The gap is
> local and fully measured: of the **fifteen** printed
> binomial-to-factorial conversions on pp. 7–8, **fourteen reproduce exactly**;
> the very first sum of the `(n^s abck)^3` group is printed without the factor
> `1/2` its own binomial side carries. The paper prints the **corrected** form
> one page later (`P008-R1` line 7 and `P008-R3` line 1 both carry
> `\frac{1}{2}`), so this looks like a dropped denominator in the p. 7 display
> rather than a mathematical error — but per this project's rules we do not
> repair it ourselves; we ask.

## Chunk + PDF ref

- chunk: `pipeline/02-chunks/chunks/M1-FRAG-05.yml` (`BLOCKED`, F4)
- signed region records: `pipeline/01-extract/regions/p006.yml` (R3, binomial
  side), `pipeline/01-extract/regions/p007.yml` (R1–R3, the conversions),
  `pipeline/01-extract/regions/p008.yml` (the corrected re-print)
- 300 dpi crops read twice by vision on 2026-09-28:
  `page-007-300dpi-region-02.png`, `page-007-300dpi-region-03.png`

## What we formalized (plain math)

`M1-FRAG-05` is the step "rewrite the binomial coefficients of the fifteen
`l+j <= 4` boundary sums of p. 6 in the author's factorial form". For the group
where the power of `(n^s abck)` is 3, the four sums are the pairs
`(j,l) = (0,3), (1,2), (2,1), (3,0)` with

```
(j,l) binomial side:  (-1)^j C(n-1-i,j) C(i,l)      range i in [l, n-1-j]
```

and the intended Lean statement is the identity of that group with the printed
factorial form, per sum, over `5 <= n`. Fourteen of the fifteen conversions are
exactly `Nat.choose`-to-falling-factorial rewrites. One is not:

| (j,l) | binomial side | printed p. 7 | factor |
|---|---|---|---|
| (0,3) | `+ i(i-1)(i-2)/6` | `+ (1/6) i(i-1)(i-2)` | 1 |
| (1,2) | `- i(i-1)(n-1-i)/2` | `- (1/2) i(i-1)(n-1-i)` | 1 |
| **(2,1)** | **`+ i(n-1-i)(n-2-i)/2`** | **`+ i(n-1-i)(n-2-i)`** | **2** |
| (3,0) | `- (n-1-i)(n-2-i)(n-3-i)/6` | `- (1/6) (n-1-i)(n-2-i)(n-3-i)` | 1 |

## What failed (sympy counterexample, no Lean)

    docker compose exec -T lean python /workspace/pipeline/04-sympy/m1f5_screen.py

exit 0, prints (shortened):

```
n=13  a,b,c,k,h,s = 2,3,5,7,11,1  (X = 2730)
  pairs checked      : 15
  pairs mismatching  : 1
    (j,l)=(2, 1): binomial side = 13542000754032092876962160984728499343478025572263473089633428153000
               printed  side = 27084001508064185753924321969456998686956051144526946179266856306000
                  -> printed / binomial = 2
  total of the fifteen sums: binomial 274848382072973662799299296664200884279923280221218207008213547813329251381
                          printed  274848395614974416831392173626361869008422623699243779271686637446757404381  (equal: False)
```

Same outcome at `n = 17` and `n = 19` (`printed / binomial = 2` in every case);
the whole display is unequal on both sides. The screen is exact integer
arithmetic with the printed ranges and the printed coefficients — no Lean, no
symbolic assumption.

## Minimal example

No sums needed. At `n = 13`, `i = 1`, the `(j,l) = (2,1)` summand has

```
binomial side : (-1)^2 C(13-1-1, 2) C(1,1) = C(11,2) = 55
printed side  : i(n-1-i)(n-2-i)            = 1*11*10 = 110 = 2 * 55
```

Term by term on that one summand the printed coefficient is exactly twice the
binomial one.

## Where the print agrees with us

The same sum appears four times in the paper:

| region | printed | source |
|---|---|---|
| `P007-R2` l0 | `+ \sum_{i=1}^{n-3} i(n-1-i)(n-2-i) ...` — **no coefficient** | signed record + two vision reads |
| `P007-R3` l2 | `+ \sum_{i=1}^{n-3} i(n-1-i)(n-2-i) ...` — **no coefficient** (re-print) | signed record + vision read |
| `P008-R1` l7 | `+ \frac{1}{2}\sum_{i=1}^{n-3} i(n-1-i)(n-2-i) ...` | signed record |
| `P008-R3` l1 | `+ \frac{1}{2}\sum_{i=1}^{n-3} i(n-1-i)(n-2-i) ...` | signed record |

`P008` is the page where the same identity is restated modulo `n^{4s+2}`, and it
carries the `1/2`. (The p. 9 and p. 11 lines that also print this summand are
the *definition* of `B`, which clears denominators by the "Quy ước" convention
of `P009-R2`, so they are not evidence either way.)

## Question for the author

On p. 7 (both places where it is printed), is the first `(n^s abck)^3` sum
missing the factor `1/2` that its binomial form
`(-1)^2 C_{n-1-i}^{2} C_i^{1}` carries and that p. 8 prints —
i.e. is the intended line
`+ \frac{1}{2}\sum_{i=1}^{n-3} i(n-1-i)(n-2-i) h^{n-3-i} b^{n(i-1)} (n^s abck)^3`
? A one-word confirmation is enough; we will then encode the corrected
coefficient and record the p. 7 print as a typo in the chunk notes.

## Attachments

- `pipeline/04-sympy/m1f5_screen.py` (the screen above; exact integers, exits 0
  iff this finding reproduces)
- `pipeline/02-chunks/chunks/M1-FRAG-05.yml` (the blocked chunk, with the frozen
  transcription of both sides)
- `pipeline/01-extract/regions/{p006,p007,p008}.yml` (signed) and the two crops
  `page-007-300dpi-region-02.png`, `page-007-300dpi-region-03.png`
- `pipeline/03-lean/M1_LANE.md` §7 (the lane's triage log)
