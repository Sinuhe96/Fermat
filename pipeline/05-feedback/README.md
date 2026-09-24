# Author feedback (`05-feedback/`)

When Lean verification fails on a chunk, the failure belongs to one of two
worlds: OUR transcription/formalization is wrong, or THE PROOF STEP is
wrong or has a gap. This track produces, for the second world, an artifact
the original author can answer quickly — without reading Lean.

## Triage rule (decide within one session, never let a failure sit)

1. Re-run the chunk's sympy test. Counterexample found → suspect OUR
   transcription first: re-check `source_text` against the PDF.
2. If transcription is faithful and sympy still refutes it → the CLAIM is
   false as stated. Open a query (template below).
3. If Lean rejects a step sympy cannot refute → the step may have a GAP
   (uses an unproven sub-claim). Open a query asking for the missing
   justification, quoting the exact inference.
4. If OUR formalization is wrong (chunk faithful, claim true, Lean stub
   mismodelled) → fix the Lean file, no query needed.

Never open a query until steps 1–4 rule out our own error. Every query
must reproduce WITHOUT Lean: sympy script + numbers, or a quoted
inference with page/line reference.

## Query file format (`queries/Q-NNN-short-title.md`)

- Heading: `# Q-NNN title [OPEN|ANSWERED|RESOLVED]`.
- Sections: Chunk + PDF ref / What we formalized (Lean statement in
  plain math) / What failed (Lean error or sympy counterexample, with
  reproduction command) / Minimal example (smallest numbers/formulas
  showing the issue) / Question for the author (one precise question) /
  Attachments (sympy script path, Lean file path, PDF screenshot).
- Status lifecycle: OPEN → ANSWERED (author replied, fix pending) →
  RESOLVED (chunk updated, Lean compiles, sympy passes; link the commit).

## Response kit

Each RESOLVED query keeps its reproduction artifacts so the author (or a
referee) can re-run them: the sympy script stays in `04-sympy/`, the Lean
file stays in `03-lean/`, and the query records both paths plus the
resolving commit hash.
