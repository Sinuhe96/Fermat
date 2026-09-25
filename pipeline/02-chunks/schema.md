# Chunk schema (contract for 02-chunks/chunks/*.yml)

Every chunk is a human-verified record. The pipeline trusts NOTHING that
is not in a chunk file passing this schema.

```yaml
id: L7-FRAG-01            # stable id, never reused
title: Lemma 7 fragment — non-divisibility conclusion
pdf_pages: [1, 2]         # source pages in PROOF_of_FERMAT.pdf
kind: lemma-statement     # lemma-statement | lemma-proof-step | definition | case-split
depends_on: []            # chunk ids that must be DONE first
source_text: |            # verbatim transcription (Vietnamese + math as-is)
  ...
formal_hint: |            # informal reading: what the Lean statement should say
  ...
transcription: manual | extract-verified
  # manual = typed by a human (required for math-dense pages 7-29)
  # extract-verified = copied from extract output AND token_overlap OK
lean_file: 03-lean/Pilot/Basic.lean     # where the formalization lives
sympy_test: 04-sympy/test_l7_frag_01.py # numeric smoke test for this chunk
source_pdf_sha: 721c2539…               # sha256 of PROOF_of_FERMAT.pdf (extraction run)
extract_run_sha: f25efc62…              # sha256 of 01-extract/out/extract_meta.json
fidelity: PASS_WITH_MANUAL              # fidelity_check.py overall verdict for the run
renders: L7_stmt_p1.png L7_proof_p4a.png  # render reads backing the transcription
lean_decls: L7_frag_01                  # comma-separated Lean decls, one per author step
status: TODO | IN_PROGRESS | BLOCKED | DONE
  # BLOCKED = gated on BLOCKERS.md entry or on an OPEN author query;
  # name the blocker/query id in status.tsv notes.
```

DONE criteria (all required):
1. `lean_file` compiles with `lake env lean` (no sorry, no warnings-as-errors).
2. `sympy_test` passes for n in {5, 7, 11, 13}.
3. Every id in `depends_on` is DONE.
4. `source_text` matches the PDF page (second pair of eyes or screenshot diff).
5. If Lean or sympy refutes the chunk: triage per `05-feedback/README.md`.
   A chunk whose failure is referred to the author goes to BLOCKED with the
   query id in status.tsv notes — never back to TODO silently.
6. The evidence block is complete and bound to ONE extraction run:
   `source_pdf_sha`, `extract_run_sha`, `fidelity`, `renders`, `lean_decls`
   (machine-checked by `pipeline/progress.py --check` for every DONE chunk).
   `renders` is REQUIRED whenever any page of `pdf_pages` has fidelity
   verdict MANUAL — the render read is that page's transcription review.
   Renders named `page-*.png` (produced by `render_pdf.py`) must carry
   their provenance sidecar (same stem, `.json`).
7. Machine checks of criteria 1 and 4: every `lean_decls` name occurs in
   `lean_file`; `lean_file` contains no `sorry`; every page in `pdf_pages`
   has fidelity verdict OK (or MANUAL with the render read recorded).
