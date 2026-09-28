# Q-003 Results (16) and (26) are cited at the final step but printed nowhere [OPEN]

> **Status: OPEN.** One inference is **F4** under AGENTS.md (the printed
> justification is a citation to a result that does not exist in the document);
> everything else here is a labelling defect with the printed mathematics intact.
> **No chunk is blocked:** pp. 31–33 are not yet transcribed (the Lean lane is at
> p. 10), so this query is filed ahead of the leaf that would hit it — p. 32 is
> where the case split closes and produces the contradiction, which makes it the
> highest-risk site in the proof. Found by an automated citation index over the
> signed region records, reproducible in one command without Lean.

## Chunk + PDF ref

- PDF: `PROOF_of_FERMAT.pdf`, §D (main proof), final case split
  - `p. 31` R2–R3: `(23)`, `(24)`, `(25)` and the two **unlabelled** displays
    that close R3
  - `p. 32` R1: the `(27)` derivation and the step that closes the case
  - `p. 32` R2: the `h − b^n ≡ a^n ≡ −b^n (mod n^s)` step
- signed region records: `pipeline/01-extract/regions/p031.yml`,
  `p032.yml` (`P031-R2`, `P031-R3`, `P032-R1`, `P032-R2`)
- 300 dpi crops read while writing this query:
  `01-extract/out/page-032-300dpi-region-01.png`,
  `page-032-300dpi-region-02.png`

## Item 1 — `(26)` is cited, never printed, and its slot carries the only unproved inference

p. 32 R1, line 4 (math quoted verbatim from the signed record):

```
⇒ H(c^n,b) ≡ H(c^n,a) ≡ 0 (mod n^{s+1})     (followed by: "suy ra từ (26) và (27)")
```

The citation is **`(26)` and `(27)`**. `(27)` is printed one line above:

```
⇒ a^{n(n−2)} + b^{n(n−2)} − c^{n(n−2)} ≡ 0 (mod n^{s+1})   (27)
```

**`(26)` is never printed.** The author's numbering runs `(24)`, `(25)` on p. 31
and then jumps to `(27)` on p. 32; scanning all 33 pages, `(26)` occurs exactly
once in the document — as this citation.

The display that must be `(26)` is printed **without a number** at p. 31 R3
lines 0–1 (`(1−n)a^n[a^{n(n−2)}+b^{n(n−2)}−c^{n(n−2)}]/(c^n−b^n)^3 −
(1−n)b^n[…]/(c^n−a^n)^3 ≡ 0 (mod n^{s+1})`), i.e. the reduction of (25) by way
of (17) and (17′) — the lead-in line at the end of p. 31 R2 announces exactly
this derivation ("Theo tính chất của H(h,b) và H(h,a) ứng với h = c^n (PT (17)
và PT(17')) và PT (25) ta có").

**Why the missing number is not cosmetic.** From the printed `(25)` one gets only

```
H(c^n, b) − H(c^n, a) ≡ 0 (mod n^{s+1})          (25)
```

— *equality*, not zero. As printed, the step above asserts **both are ≡ 0**. The
inference "equal to each other ⇒ both zero" is nowhere in the printed text, and
it is the one link the rest of the case needs: the next line uses `H(c^n,b) ≡ 0`
together with `(23)` to force

```
(3/2)·a^{n(n−1)}(n^s abck) ≡ 0 (mod n^{s+1})      then   n = 3, (vô lý)
```

which closes the case. So whether this step is sound depends entirely on what
`(26)` was meant to be.

## Item 2 — `(16)` is cited, never printed

p. 32 R2, line 6 (this line also cites `(16'')`, which *does* exist on p. 29 R2):

```
Từ (16), (28), (29), (30), (31), (32),  h − b^n ≡ a^n ≡ −b^n (mod n^s)  và
h = n^{ns−1} c^n ≡ 0 (mod n^{ns−1}),   Từ (16'') suy ra …
```

**`(16)` is never printed.** p. 29 defines `(16')` (R1) and `(16'')` (R2), but no
bare `(16)`; the numbering on pp. 24–28 defines **no** labelled display at all
(those pages carry six unlabelled congruence continuations). So the first entry
of that citation list has no referent, and the list is load-bearing: it is the
justification for `h − b^n ≡ a^n ≡ −b^n (mod n^s)`.

Both readings were checked against the render before filing, in case the
primes were lost to the document's Symbol-font/PUA encoding: the crop shows a
plain **`(16)`** for the first occurrence and a stroked `(16'')` later in the
same line; `(26)` and `(27)` are crisp. So this is what the paper prints, not a
transcription artifact.

## Item 3 — `(25)` is cited where the printed `(23)` is the one that applies

p. 32 R1, line 5:

```
⇒ (3/2)·a^{n(n−1)}(n^s abck) ≡ 0 (mod n^{s+1})     (followed by: "kết hợp với (25)")
```

To get this from `H(c^n,b) ≡ 0` one needs

```
H(c^n, b) + (3/2)·a^{n(n−1)}(n^s abck) ≡ 0 (mod n^{s+1})     (23)
```

which is what p. 31 R2 prints as `(23)`. The printed `(25)` is the *difference*
`H(c^n,b) − H(c^n,a) ≡ 0`, which yields the previous line's assertion rather
than this one. So `(25)` here looks like it should be `(23)`.

## Reproduction (no Lean, one command)

    python pipeline/01-extract/cite_index.py

Indexes every printed label against every citation site in the signed region
records, in document order, and reports forward citations, repeated labels and
citations with no printed definition. Its output for the whole document:
`52 definitions, 82 citations, 37 labels`, with the two DANGLING rows being
exactly `(16)` and `(26)` at the sites above. Exit 0. The same run reports **no
forward citation anywhere in pp. 1–33** — every other cited result is printed
before it is used.

## Question for the author

1. **What is `(26)`?** Is it the unlabelled p. 31 R3 display (in which case only
   the number is missing), or a line that was left out of the proof? And from
   which printed step does `H(c^n,b) ≡ H(c^n,a) ≡ 0` follow — i.e. what makes
   the two `H` values **zero** rather than merely equal?
2. **What is the first entry of the `Từ (16), (28), …` list on p. 32 R2?** Is it
   `(16′)`, `(16″)`, or a display from pp. 24–28 that should have been numbered
   `(16)`?
3. **Is the `(25)` on p. 32 R1 line 5 meant to be `(23)`?**

## Attachments

- `pipeline/01-extract/cite_index.py` — the citation index (the reproduction)
- `pipeline/01-extract/out/citations.tsv` — every label site and citation site
- `pipeline/01-extract/regions/p031.yml`, `p032.yml` — the signed records quoted
- crops: `page-032-300dpi-region-01.png`, `page-032-300dpi-region-02.png`
- `pipeline/03-lean/M1_LANE.md` §7 "Circularity audit" — full analysis, including
  the ordering cross-check against the Lean chunk dependencies
