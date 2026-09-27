# Q-002 Two under-printed steps in bổ đề 7's remaining conclusion groups [EDITORIAL]

> **Status: EDITORIAL, not blocking.** Both items are **F3** under AGENTS.md's
> classification: the printed *conclusions* are correct and fully derivable
> from the author's own material, so they were encoded in-lane (no new
> assumption, no changed hypothesis) and the chunks are DONE:
> `L7-FRAG-06` (item 1) and `L7-FRAG-05` (item 2). Nothing in the printed
> mathematics needs repair; the two notes below concern how much of the
> derivation the p. 5 proof spells out.

## Chunk + PDF ref

- Chunks: `L7-FRAG-06` (`pipeline/02-chunks/chunks/L7-FRAG-06.yml`),
  `L7-FRAG-05` (`pipeline/02-chunks/chunks/L7-FRAG-05.yml`)
- PDF: `PROOF_of_FERMAT.pdf`
  - statement list: p. 1 bottom → **p. 2 top** (the conclusion list of bổ đề 7)
  - proof: **p. 4 bottom → p. 5** ("7. Chứng minh bổ đề 7"; the closing bullet
    "Vì n ≡ 1 (mod 6), nên n = 6l + 1, …")
  - use site: **p. 30 R2** ("Từ (17), (21), (22), ta có …")
  - signed region records: `pipeline/01-extract/regions/p002.yml` R1,
    `p005.yml` R2, `p030.yml` R2
  - 300 dpi crops read: `01-extract/out/page-002-300dpi-region-01.png`,
    `page-005-300dpi-region-02.png`

## Item 1 — (22) is stated and cited, but never derived

The p. 2 statement list contains

```
a^{n(n−3)} + b^{n(n−3)} + c^{n(n−3)} ≡ 0 (mod n²)                       (22)
```

and the main proof consumes it at p. 30 R2 together with (17) and (21). The
p. 5 proof, however, derives only the `a^{n(n−4)}` group (21) and then closes
the bullet; no line of the printed proof reaches (22).

**What we encoded (F3).** `L7F6_step_S21` derives it from material the author
has already established one page earlier:

```
a^{n(n−3)} = a^n · a^{n(n−4)}                        (exponent identity)
a^{n(n−4)} ≡ b^{n(n−4)} ≡ −c^{n(n−4)}      (mod n²)  (21)
c^n ≡ a^n + b^n                            (mod n²)  (b)
--------------------------------------------------------------
a^{n(n−3)} + b^{n(n−3)} + c^{n(n−3)}
      = c^{n(n−4)} · (c^n − a^n − b^n) ≡ 0 (mod n²)
```

Independently screened on real instances: `04-sympy/test_l7_frag_06.py`
(56,844 witnesses at n = 5, 7, 11, 13; the (22) congruence holds on all of
them).

**Editorial suggestion.** Add the two-line derivation above to the p. 5
closing bullet (or write "(22) tương tự" next to (21)), so a reader does not
have to reconstruct it from (21)+(b).

## Item 2 — the printed mod-`n` line in the `n ≡ −1 (mod 6)` reductio

In the S16 reductio the printed chain reads

```
a^{3n(2l−1)} + b^{3n(2l−1)} − c^{3n(2l−1)} ≡ 0 (mod n)
⇒ a^{3n(2l−1)} + a^{3n(2l−1)} + a^{3n(2l−1)} ≡ 0 (mod n²)
```

The first line's modulus is `n`, but the line after it works mod `n²`, and the
substitutions `b^{3n(2l−1)} ≡ a^{3n(2l−1)}` and
`c^{3n(2l−1)} ≡ −a^{3n(2l−1)}` need exactly the mod-`n²` forms (19)/(20) —
which the print itself cites at that point. With the mod-`n²` reading the whole
reductio is correct (and is what `L7F5_step_S16` encodes, giving
`3·a^{n(n−2)} ≡ 0 (mod n²)`, hence `n ∣ a`, contradicting `a ⋮̸ n`).

**Editorial suggestion.** Print that line at modulus `n²` (the modulus (22')
and (19)/(20) carry, and the one the next line uses).

## Evidence that the classification is F3 and not F4

- the conclusions are the printed ones, unmodified (`L7F6_step_S21`,
  `L7F5_step_S16` statements in `03-lean/L7F6/Basic.lean`,
  `03-lean/L7F5/Basic.lean`);
- both derivations use only the author's own earlier steps — (21), (b),
  (19)/(20), (22') — and no new hypothesis;
- both are screen-verified on real instances
  (`04-sympy/run_all_20260928.log`, 13/13 tests pass);
- the Lean encodings are S1: EXIT 0, zero warnings, no `sorry`, permitted
  axioms only (`03-lean/probes/L7-ASM.axioms.lean`).
