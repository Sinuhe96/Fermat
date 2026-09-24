# Q-000 EXAMPLE — how to file an author query [OPEN]

> This is a TEMPLATE. Copy it as `Q-001-...md` for the first real query.
> Delete this file when the first real query exists (progress.py counts
> `Q-*.md`, so the template would inflate the total).

## Chunk + PDF ref

- Chunk: `L7-FRAG-01` (`pipeline/02-chunks/chunks/L7-FRAG-01.yml`)
- PDF: `PROOF_of_FERMAT.pdf`, p. 2, displayed congruence (3rd line)

## What we formalized

For prime n > 3 and integers a, b, c with n ∤ abc,
hypotheses H1, H2 imply `(a^n − b^n)(c^n + a^n)(c^n + b^n) ≢ 0 [n]`.

## What failed

[ILLUSTRATIVE NUMBERS — replace with the real failure when filing.
This template ships with a made-up example so the shape is clear.]

`04-sympy/test_l7_frag_01.py` found a counterexample:
n = 7, (a, b, c) = (2, 3, 5) gives product ≡ 0 (mod 7) while H1, H2 hold.

Reproduce: `python pipeline/04-sympy/test_l7_frag_01.py`

## Minimal example

[ILLUSTRATIVE — fill in the real minimal numbers when filing; the point is
the author sees numbers, not Lean. Current pilot smoke passes with zero
counterexamples, so no real example exists yet.]

## Question for the author

Is hypothesis H2 (the `n(n−2)`-power congruence) perhaps mis-copied from
p. 2, or does the conclusion need the extra condition a, b, c distinct?

## Attachments

- sympy: `pipeline/04-sympy/test_l7_frag_01.py`
- Lean: `pipeline/03-lean/Pilot/Basic.lean`
- PDF screenshot: `05-feedback/assets/Q-000-p2.png` (attach when filing)
