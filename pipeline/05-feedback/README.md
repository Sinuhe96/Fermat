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

## Author report (`render_report.py`)

Send the author a package they can answer **without Lean**:

    python pipeline/05-feedback/render_report.py

Reads `queries/Q-NNN-*.md` plus the chunk records (`02-chunks/chunks/*.yml`)
and writes `report/`:

- `report/index.html` — overview: the open queries, chunk status, and how to
  respond (bilingual vi/en chrome, query text kept verbatim);
- `report/Q-NNN.html` — one page per issue, in reading order: the question
  first (highlighted card), what the print says, the PDF renders embedded
  (`renders` of the chunk + any image the query cites, so the disputed line is
  on screen), what Lean formalized plus the verified declaration list, the
  F3/F4 classification notes, and a reply box (screen textarea, ruled lines
  when printed);
- `report/reply-Q-NNN.md` — plain-text reply template for answering by email.

While building it, the script cross-checks the ledger: every `BLOCKED` chunk
must be referenced by a query, every query must point at an existing chunk,
and every cited image/render must exist. Warnings are printed and shown in
`index.html` (the report is still written). Exit codes: 0 report written
(warnings allowed), 1 no query / unparseable query, 2 output not writable.

`report/` is generated — never hand-edit it; re-run the script when a query
changes and commit the refreshed output together with the query.
