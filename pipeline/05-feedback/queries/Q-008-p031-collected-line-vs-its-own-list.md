# Q-008 p. 31's collected line is not the collection of its own 17-term list [OPEN]

> **Status: OPEN.** On p. 31 the author lists seventeen terms, every one carrying
> exactly one factor `(n^s abck)`, and then collects them into a four-term line.
> At modulus `n^{s+1}` nothing else can survive, so the second line must be the
> coefficient-wise collection of the first. It is not: one coefficient is printed
> `−2/3` where the list gives `−4/3`, and two monomials that the list produces
> (`a^n b^{n(n−2)}` with `+1/2` and `a^n c^{n(n−2)}` with `−1/2`) have no
> counterpart in the printed line at all. Three of the five coefficients match
> exactly, which is the internal control that the reading is right.

## Chunk + PDF ref

- chunk: `M1-FRAG-37` (p. 30–31, the bổ đề 7 use #1 and the `(18)`–`(22′)` chain)
  is the consumer; it is not started
- signed region record: `pipeline/01-extract/regions/p031.yml` (region `P031-R2`)
- 300 dpi crop: `page-031-300dpi-region-02.png`

## What we formalized (plain math)

The long display carries seventeen terms of the form `c · (n^s abck)`; the line
after it prints

```
⇒ H(c^n, b) + (2/3) c^n a^{n(n−2)} (n^s abck) − (2/3) b^{n(n−3)} a^{2n} (n^s abck)
   + (5/6) a^{n(n−1)} (n^s abck) ≡ 0 (mod n^{s+1})
```

Collecting the long list by monomial gives

```
(5/6) a^{n(n−1)} + (2/3) c^n a^{n(n−2)} − (4/3) b^{n(n−3)} a^{2n}
  + (1/2) a^n b^{n(n−2)} − (1/2) a^n c^{n(n−2)}   (times n^s abck).
```

## What failed (exact rational arithmetic, no Lean)

    docker compose exec -T lean python /workspace/pipeline/04-sympy/sweep_constants.py

check C2, exit 0 (abridged):

```
[OK ] P031-R2  X=a^{n(n-1)}: printed=5/6 computed=5/6
[OK ] P031-R2  W=c^n a^{n(n-2)}: printed=2/3 computed=2/3
[CONTRADICTION] P031-R2  Z=b^{n(n-3)}a^{2n}: printed=-2/3 computed=-4/3
[CONTRADICTION] P031-R2  Y=b^{n(n-2)}a^n (printed: absent): printed=0 computed=1/2
[CONTRADICTION] P031-R2  T=c^{n(n-2)}a^n (printed: absent): printed=0 computed=-1/2
[CONTRADICTION] P031-R2  collected == printed
[OK ] P031-R2  (23): 2/3 + 5/6: printed=3/2 computed=3/2
```

The last line is relevant context, not a defence: the *next* numbered step (23)
does legitimately add the printed `2/3` and `5/6` to reach `3/2`, so the slip is
more likely in the long list than in its collected form — but the lane does not
choose: the two printed lines cannot both stand.

## Minimal example

Set the free monomials to `1` (i.e. compare coefficients): the two printed
quantities differ by exactly

```
(n^s abck) · ( 1/2·a^n b^{n(n−2)} − 1/2·a^n c^{n(n−2)} − 2/3·b^{n(n−3)}a^{2n} ),
```

whose coefficient at `a = b = c = 1` is `1/2 − 1/2 − 2/3 = −2/3 ≠ 0`.

## Question for the author

Two questions, in the author's own order of preference:

1. Which of the two printed lines is the intended one — the seventeen-term list
   or the collected four-term line?
2. If the collected line is intended, what removes the two monomials
   `a^n b^{n(n−2)}` (`+1/2`) and `a^n c^{n(n−2)}` (`−1/2`)? The section prints no
   congruence relating them (the (18)–(22′) facts do not), and neither appears in
   the collected line.

## Attachments

- `pipeline/04-sympy/sweep_constants.py` (check C2; exact rationals)
- `pipeline/01-extract/regions/p031.yml` (signed) and the crop
  `page-031-300dpi-region-02.png` (re-read for both displays, including the
  bracket contents)
- `pipeline/03-lean/M1_LANE.md` §7
