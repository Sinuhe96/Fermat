# AGENTS.md — operating rules for this repository

These rules are binding on any agent working here. They exist to prevent
repeated, expensive mistakes. When in doubt, follow this file over
general coding habits.

**Starting a fresh session:** read `HANDOFF.md` first for the live status
and exact next step, then follow the rules below. `README.md` covers the
environment; this file governs how we work.

## Mission

We are building a **formalized verification** of an existing proof of
Fermat's Last Theorem found in `PROOF_of_FERMAT.pdf` (Vietnamese, 33
pages). The proof is complete and already written. We are NOT proving the
theorem ourselves, and we are NOT writing a new proof.

## THE core rule: verify the author's proof, not our own

The proof lives in the PDF. We transcribe the AUTHOR's deductive chain
into Lean, and Lean verifies whether THAT chain is correct.

- **Transcribe the PDF's proof verbatim** — every hypothesis, every
  substitution, every mod reduction, in the author's order.
- **Re-encode that same chain in Lean** — each author step becomes a Lean
  step mirroring their reasoning (same intermediate claims, same order).
- **Lean is the checker.** It certifies the author's chain of inferences,
  or exposes the first step that fails.
- A Lean rejection of a faithfully-transcribed step is a REAL FINDING
  about the proof (a gap or an error). File it to the author per
  `pipeline/05-feedback/README.md` — do not work around it.

### What we must NEVER do

- Do NOT invent, derive, or substitute our own proof. If we prove a
  reformulation, we have NOT verified the author's work — we have written
  a different, weaker artifact.
- Do NOT silently "fix" an author's step that Lean rejects. If our
  transcription is faithful and Lean rejects it, that is a finding for the
  author. Only "fix" when our OWN transcription is wrong.
- Do NOT treat a conclusion statement as the chunk. The chunk must carry
  the author's actual proof steps, not just the headline result.

### The transcription-speed rule (why we stay in this lane)

Transcription is cheap: decode the author's steps from the relevant PDF
renders and encode each as a Lean step. There is nothing to derive. If a
task starts to feel like proof research, stop: re-read the PDF proof and
return to the first author step not yet represented in Lean.

Mathlib usually contains the elementary mathematics needed here, but its
names, types, hypotheses, and normal forms may differ from the paper. It is
legitimate to search for the exact Mathlib API, prove type/cast bridges, and
make implicit side conditions explicit. It is not legitimate to search for
a different mathematical route to the conclusion.

## Required preparation for every Lean session

Before editing a Lean proof:

1. Read `HANDOFF.md` and identify the one current chunk and exact next step.
2. Run `python pipeline/smoke/smoke_pipeline.py`. If it fails, fix the
   environment before touching the mathematics.
3. Read the chunk YAML, its rendered PDF source pages, and its dependencies.
4. Read `pipeline/03-lean/MATHLIB_API_LESSONS.md`,
   `pipeline/03-lean/ENCODING_MAP.md` (notation → Lean terms, per-chunk
   reusable patterns) and `.github/skills/fermat-lean-mathlib/SKILL.md`.
5. Verify that the chunk has two distinct records:
   - literal source transcription, preserving signs, exponents, modulus,
     labels, and order;
   - normalized ordered step map, with one entry per author inference.
6. Confirm the first author step not yet accepted by Lean. Work only on that
   step; do not write ahead or attack the final theorem directly.

If the exact source is ambiguous, stop before Lean work and obtain a second
visual transcription. OCR or extracted text is navigation help only; the
rendered PDF is authoritative.

## One-step verification loop

For each author step, in source order:

1. Record its source page/region, exact premises, exact conclusion, cited
   result, substitution, and modulus.
2. Run a cheap Sympy witness search when the claim is computational. A
   witness disproves the transcription or step; no witness is only a smoke
   result, never a proof.
3. Encode exactly that step as one named Lean claim. Add only formal details
   that paper convention leaves implicit: casts, nonzero facts, bounds,
   parity, typeclass instances, exponent identities, and cancellation
   conditions.
4. Compile immediately. After an error, do not add later tactics or later
   author steps.
5. Search Mathlib only for the current error or bridge. Search pinned local
   sources first, batch candidate checks into one script, and use one
   container round-trip. Set a bounded search: after local search plus one
   batched candidate check fails, classify the outcome below instead of
   starting open-ended proof research.
6. Save the compiler message, source quotation, and attempted faithful Lean
   encoding as evidence for the classification.

## Mandatory outcome classification: four failures or one success

Every attempted author step must end in exactly one of these five outcomes.
Agents must state the classification explicitly in the chunk notes or
handoff before continuing or stopping.

### F1 — Transcription or chunk-model error

Evidence: the Lean claim, Sympy witness, or second visual check does not match
the rendered PDF; a sign, exponent, modulus, hypothesis, dependency, or step
boundary was copied incorrectly.

Action: correct our transcription/chunk record, rerun the cheap checks, and
retry the same author step. This is the only class in which changing the
formalized statement is routine. Never attribute this failure to the author.

### F2 — Lean encoding or Mathlib API error

Evidence: the paper step is clear, but Lean reports a syntax/type/cast/
instance/normal-form problem, or the attempted Mathlib lemma has the wrong
API. The mathematical implication itself has not been rejected.

Action: repair only the representation or API bridge. Consult the pinned
Mathlib source and project API lessons. Preserve the source claim and its
place in the chain. If the bounded search is exhausted, record the exact
technical blocker and hand it off; do not replace the proof step.

### F3 — Missing explicit side condition

Evidence: Lean exposes a condition the paper treats implicitly, such as a
nonzero divisor, positivity bound, odd exponent, coprimality fact, modulus
reduction, or preservation of hypotheses under a stated substitution.

Action: first trace the condition to existing author hypotheses or a cited
standard theorem. If it follows routinely, encode that derivation immediately
before the step and continue. If it requires a new mathematical assumption or
nontrivial argument absent from the source, reclassify as F4; do not invent it.

### F4 — Faithful author step unsupported

Evidence: transcription has been independently checked; the Lean types and
API bridge are correct; all side conditions justified by the source have been
supplied; yet the stated conclusion does not follow, a counterexample exists,
or a required assumption/inference is absent from the author's text.

Action: stop the chunk at this first unsupported step. Do not prove around it,
strengthen hypotheses, repair a sign, or continue downstream. Mark the chunk
`BLOCKED` and create an author-actionable query according to
`pipeline/05-feedback/README.md`, including the source quotation, plain-language
issue, minimal reproduction/counterexample when available, and Lean error or
unsolved goal.

### S1 — Faithful step verified

Evidence: Lean compiles the claim without `sorry`, custom axioms, changed
hypotheses, or an alternative proof route, and the claim is visibly mapped to
the corresponding author step.

Action: record the accepted step and move to the next author step. A chunk is
DONE only after every step receives S1, dependencies are DONE, Sympy smoke
checks pass, the complete file compiles, and `#print axioms` shows only the
permitted standard axioms.

## Who judges a disputed classification?

Lean is the formal judge of whether the encoded implication typechecks. The
rendered PDF is the authority for what the author wrote. Neither Lean nor an
AI decides authorial intent where the PDF is ambiguous.

A second agent or external model (including Jev, if configured) may act as an
**independent reviewer**, not as an authority. Consult it only after the first
agent has produced a compact evidence packet: source image coordinates and
literal transcription, normalized premises/conclusion, minimal Lean snippet,
compiler output, Sympy result, and proposed F1/F2/F3/F4 classification. The
reviewer must classify independently and may identify a transcription or API
mistake. It may not invent a proof, reinterpret an unexplained sign, or
supersede a Lean failure. If reviewers disagree after checking F1–F3, choose
F4 and ask the author rather than spending more proof-search resources.

## Sequencing and smoke gating

Work one chunk at a time, in strict source order, gating each expensive step
behind a cheap check:

1. Freeze the literal transcription and ordered author-step map.
2. Record and verify all cited dependencies.
3. Sympy-screen the statement and computational intermediate claims.
4. Encode and classify one author step at a time using F1–F4 or S1.
5. Stop immediately on F4; continue only after S1.
6. At chunk completion, compile in the Linux work volume, check for `sorry`
   and unexpected axioms, then update `status.tsv`, chunk YAML, and generated
   `pipeline/PROGRESS.md`.

Run `python pipeline/smoke/smoke_pipeline.py` before any large work — if it
is red, fix the machine, not the math.

## Cost classes (do the cheap thing on the right side)

- **Transcription:** minutes; done from the PDF renders.
- **Sympy witness search:** instant; done on the host (Windows Python).
- **Mathlib lemma verification:** one slow-ish `lake env lean` round-trip;
  batch all name-checks into ONE script, exec once.
- **Lean compile against Mathlib:** only inside the `lean` container, and
  NEVER on the Windows bind mount (9p drvfs deadlocks the cache fetch).
  Lake work happens in `/workspace/work` (Linux `lake-work` volume);
  `proof/` and `proof_verify/` are edit-only.

## Tooling pitfalls that have already wasted time

- PowerShell does not parse bash-isms: `cat <<EOF`, `&&`, and `| tail`
  fail or misbehave. Use the Linux tool for POSIX commands, or write a
  script file and exec it once.
- Batch container round-trips. One script per session, exec once — never
  one command per round-trip through a fragile shell bridge.
- CRLF: `.gitattributes` forces `eol=lf`. Never add Linux scripts via
  Windows tools that inject CRLF (the `\r` shebang broke `#!/bin/sh`).

## Where the contracts live

- `pipeline/PIPELINE.md` — stage-by-stage pipeline description.
- `pipeline/02-chunks/schema.md` — chunk record contract (DONE criteria).
- `pipeline/02-chunks/chunks/*.yml` — per-chunk records.
- `pipeline/05-feedback/README.md` — author-feedback triage and format.
- `pipeline/progress.py` + `pipeline/PROGRESS.md` — live status dashboard.
- `README.md` — quick start and environment.
- `pipeline/03-lean/MATHLIB_API_LESSONS.md` — Mathlib API pitfalls and
  workarounds discovered during the first chunk (ZMod, linarith, pow_mul,
  FLT). **Read this before encoding any Lean proof.**
- `pipeline/03-lean/ENCODING_MAP.md` — the PDF's notation → Lean/Mathlib
  term mapping (gcd, `⋮`, congruences, "chứng minh tương tự", …) plus the
  proof patterns that already compiled, one section per chunk. Read
  alongside the API lessons; append a section per new chunk.
- `.github/skills/fermat-lean-mathlib/SKILL.md` — the project's Lean 4 +
  Mathlib skill: toolchain pin, container compile loop, lemma-search
  ladder, naming conventions, error→fix table. Read it alongside
  `MATHLIB_API_LESSONS.md` before encoding or searching for lemmas.

Docker builds maintain stable-to-volatile layering with a tiny context
and persistent volumes (see `Dockerfile`, `compose.yml`, `.dockerignore`)
so a rebuild after any error resumes from the last good layer instead of
starting over.