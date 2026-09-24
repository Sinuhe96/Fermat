# AGENTS.md — operating rules for this repository

These rules are binding on any agent working here. They exist to prevent
repeated, expensive mistakes. When in doubt, follow this file over
general coding habits.

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

Transcription is cheap: decode the author's steps (from the PDF renders,
which are readable on pp1–2) and encode each as a Lean step. There is
nothing to derive. If a task starts to feel like proof research, we have
left the mission — stop and re-read the PDF proof.

## Sequencing and smoke gating

Work one chunk at a time, in a strict order, gating each expensive step
behind a cheap check so we never submit long work with a trivial mistake:

1. **Transcribe faithfully** (from the PDF, not from memory). Freeze the
   chunk's statement AND its author proof steps.
2. **Sympy smoke test before Lean** (cheap, on host): any numeric
   counterexample means the transcription is wrong. Fix the chunk, never
   prove a false lemma.
3. **Encode the author's chain in Lean.**
4. **Lean compiles the author's chain**, or reports the first failing step.
5. **Update the ledger** (`pipeline/02-chunks/status.tsv` + chunk YAML +
   generated `pipeline/PROGRESS.md`).

Run `python pipeline/smoke/smoke_pipeline.py` before any large work — if
it is red, fix the machine, not the math.

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

Docker builds maintain stable-to-volatile layering with a tiny context
and persistent volumes (see `Dockerfile`, `compose.yml`, `.dockerignore`)
so a rebuild after any error resumes from the last good layer instead of
starting over.