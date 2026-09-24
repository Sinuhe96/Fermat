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
status: TODO | IN_PROGRESS | DONE
```

DONE criteria (all required):
1. `lean_file` compiles with `lake env lean` (no sorry, no warnings-as-errors).
2. `sympy_test` passes for n in {5, 7, 11, 13}.
3. Every id in `depends_on` is DONE.
4. `source_text` matches the PDF page (second pair of eyes or screenshot diff).
