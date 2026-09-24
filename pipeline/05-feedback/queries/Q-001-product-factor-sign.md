# Q-001 Product factor sign mismatch: a^n − b^n vs a^n + b^n [OPEN]

## Chunk + PDF ref

- Chunk: `L7-FRAG-01` (`pipeline/02-chunks/chunks/L7-FRAG-01.yml`)
- PDF: `PROOF_of_FERMAT.pdf`
  - statement: p. 1 bottom ("thì ta có (a^n − b^n)(c^n + a^n)(c^n + b^n) ≢ 0 (mod n)")
  - proof: p. 4 bottom → p. 5 top ("Vậy b^n + c^n ≢ 0 (mod n). Chứng minh
    tương tự ta cũng có a^n + b^n ≢ (mod n), c^n + a^n ≢ 0 (mod n). Tóm lại,
    ta luôn có: (a^n − b^n)(c^n + a^n)(c^n + b^n) ≢ 0 (mod n) (đpcm).")
  - text-layer line refs: `pipeline/01-extract/out/extract_pypdf.txt` lines
    1053–1057.

## What we formalized

For prime n > 3 and integers a, b, c with n ∤ abc:

- H1: a^n + b^n ≡ c^n (mod n²)
- H2: a^{n(n−2)} + b^{n(n−2)} ≡ c^{n(n−2)} (mod n)

Lean statement of the conclusion, verbatim from the PDF statement:
`(a^n − b^n)(c^n + a^n)(c^n + b^n) ≢ 0 (mod n)`.

The author's proof steps were transcribed in order (see the header of
`03-lean/Pilot/Basic.lean`): the b^n + c^n ≡ 0 contradiction, then
"chứng minh tương tự" for a^n + b^n and c^n + a^n, then "Tóm lại" for the
product.

## What failed

Lean cannot close the final "Tóm lại" step: the proof as printed establishes
non-divisibility only for the three pairwise **sums**
`b^n + c^n`, `a^n + b^n`, `c^n + a^n`, but the product's first factor is the
**difference** `a^n − b^n`, which no step of the printed chain excludes.
The exact spot is marked by the single `sorry` in
`pipeline/03-lean/Pilot/Basic.lean` (theorem `L7_frag_01`, hypothesis
`h_factor1`); every other step compiles.

Reproduction of the transcription (no Lean needed): extract lines 1053–1057

```
extract_pypdf.txt:1055  ... Chứng minh tương tự ta cũng có
extract_pypdf.txt:1055  (a^n + b^n ≢ (mod n), c^n + a^n ≢ 0 (mod n)) . Tóm lại, ta
extract_pypdf.txt:1057  luôn có: (a^n − b^n)(c^n + a^n)(c^n + b^n) ≢ 0 (mod n) (đpcm).
```

(pypdf drops superscripts; the ± signs are unambiguous. Confirmed
independently against the page renders
`pipeline/01-extract/out/L7_proof_p4a.png`, `L7_stmt_p1.png`, `z_stmt_p1.png`.)

## Minimal example

No numeric counterexample exists: `python pipeline/04-sympy/test_l7_frag_01.py`
exits 0 (n = 7: 12 witnesses, n = 13: 24 witnesses, zero with product ≡ 0).
The issue is proof coverage, not truth — the statement as printed verifies on
every witness found.

## Question for the author

In the "Chứng minh tương tự" line, should the first listed congruence read
`a^n − b^n ≢ 0 (mod n)` (matching the product in the statement and in the
"Tóm lại" line), or should the product's first factor be `a^n + b^n`
(matching the three sums actually proved)? One of the two printed signs must
be a typo; with either reading the lemma is true, but only one makes the
printed proof complete.

## Attachments

- sympy: `pipeline/04-sympy/test_l7_frag_01.py` (statement as printed: PASS)
- Lean: `pipeline/03-lean/Pilot/Basic.lean` (single `sorry` at the gap)
- PDF screenshot: `pipeline/05-feedback/assets/Q-001-p4-5-proof.png`
