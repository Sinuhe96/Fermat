# Q-007 p. 33's final coefficient is printed `55/3` where its own 14-term assembly sums to `55/4` [OPEN]

> **Status: OPEN.** The last display of the proof reads
> `⇒ (55/3) b^{n(n−1)} ≡ 0 (mod n)` and is presented as the sum of the fourteen
> coefficients listed in the display immediately above it. Those fourteen
> coefficients sum to exactly `55/4`, and a second, independent reduction of the
> grouped multi-line display above them also gives `55/4`. The conclusion of the
> case split is unaffected either way (`n | 55` gives `n ∈ {5, 11}` for both
> readings, and the main case has `n > 11`), so this is a print defect with no
> downstream effect — recorded because a verified artifact must not silently
> adopt one of two printed values.

## Chunk + PDF ref

- chunk: none yet — `M1-FRAG-41` (p. 33, the final assembly) will consume this line
- signed region record: `pipeline/01-extract/regions/p033.yml` (region `P033-R1`)
- 300 dpi crop: `page-033-300dpi-region-01.png`

## What we formalized (plain math)

The display lists fourteen coefficients of `b^{n(n−1)}`, every one of them
printed in full:

```
+4, -65/4, +4/3, +4, +1/4, -15/2, +28, -15, +1/4, +2, +16/3, -7, -5/3, +16
```

and the next line collects them into a single coefficient times
`b^{n(n−1)}`.

## What failed (exact rational arithmetic, no Lean)

    docker compose exec -T lean python /workspace/pipeline/04-sympy/sweep_constants.py

check C1, exit 0:

```
C1  P033-R1 (p.33): the 14-term  b^{n(n-1)}  assembly -> printed 55/3
   14 printed coefficients sum to 55/4 (55/4)
[OK ] P033-R1 penultimate-line sum: printed=55/4 computed=55/4
[CONTRADICTION] P033-R1 final line 55/3: printed=55/3 computed=55/4
   grouped-display coefficient sum = 55/4
[OK ] P033-R1 grouped-display coefficient: printed=55/4 computed=55/4
```

The second `[OK ]` is the independent route: the *grouped* multi-line display two
rows earlier is reduced term by term (each of its `b^{n(n−4)}(−b^n)^3`,
`b^{n(n−3)}b^{2n}`, `b^{n(n−2)}(−b^n)`, `b^{n(n−5)}b^{4n}` equals `b^{n(n−1)}`),
and its multipliers sum to `55/4` as well. So the fourteen-term list and the
grouped form agree with each other and disagree with the collected line.

## Minimal example

`55/4 = 13.75` versus `55/3 = 18.333…`; the printed line differs from its own
assembly by `−55/12 · b^{n(n−1)}`.

## Question for the author

Is the denominator of the final coefficient a `4` (so that the collected line is
the sum of the list above it, `55/4`), i.e. is the printed `55/3` a slip?

## Attachments

- `pipeline/04-sympy/sweep_constants.py` (check C1; exact rationals)
- `pipeline/01-extract/regions/p033.yml` (signed) and the crop
  `page-033-300dpi-region-01.png` (vision resolved the denominator glyph as a
  `3` and re-read all fourteen coefficients identically)
- `pipeline/03-lean/M1_LANE.md` §7 (the sweep that found it)
