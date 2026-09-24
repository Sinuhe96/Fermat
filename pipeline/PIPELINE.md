# Pipeline: PDF -> faithful text -> lemma chunks -> Lean

Stages:

1. `01-extract/` — PDF text extraction, deterministic and reproducible.
   - `extract.py` runs pypdf AND pymupdf, writes both transcripts.
   - `fidelity_check.py` compares char counts, text-presence per page, and a
     verdict file. The pipeline STOPS here if fidelity fails.
   - Why two tools: math-dense pages (7-29) extract differently per engine.
     Low prose-token overlap CONFIRMS unreliability — the two extracts
     agreeing is the signal; the diff pinpoints which pages need eyes.
   - Math pages that fail are routed to MANUAL transcription (see chunks).

2. `02-chunks/` — human-verified YAML records, one per work unit.
   - `schema.md` is the contract every chunk must satisfy.
   - `chunks/` holds chunk files (e.g. `L1-statement.yml`).
   - `status.tsv` is the checkpoint ledger: chunk, pages, status, Lean file.
   - A chunk is only DONE when Lean compiles AND sympy smoke passed AND
     cross-references resolve.

3. `03-lean/` — Lean formalization, git-versioned.
   - `Pilot/` is the FIRST chunk through (Lemma 7 fragment). It validates the
     flow before bulk work.
   - `Common/` holds shared helpers; `Main.lean` wires module roots.
   - ONLY `03-lean/` holds `.lean` files. Sympy lives one stage earlier.

4. `04-sympy/` — numeric smoke tests (n=5,7,11,13), BEFORE formalizing.
   - A hypothesis that fails numerically is a transcription error or a false
     lemma. Either way: fix the chunk, never start a proof of it.
   - `run_all.py` runs every smoke test and reports pass/fail per chunk.

5. `smoke/` — pipeline health checks (NOT math verification).
   - `smoke_pipeline.py` fails fast on: missing toolchain, Lean hello-world
     not compiling, sympy import broken, extract scripts crashing on page 1.
   - Run BEFORE any large work. If smoke is red, fix the machine, not the math.

6. `progress.py` + `PROGRESS.md` — where are we, right now.
   - `python pipeline/progress.py --check` prints the dashboard and verifies
     ledger consistency (tsv vs chunk files, unknown deps, cycles). Exit 1
     means the TRACKING is broken — fix it before trusting the picture.
   - `python pipeline/progress.py --write pipeline/PROGRESS.md` refreshes the
     committed snapshot. Regenerate whenever statuses change.
   - Sources of truth: `02-chunks/status.tsv`, chunk files, `BLOCKERS.md`,
     `05-feedback/queries/`. Never edit PROGRESS.md by hand.

7. `BLOCKERS.md` — obstacle log (technical: toolchain, cache, RAM).
   - One `## B-NNN ... [OPEN|RESOLVED]` section each, newest on top.
   - An entry closes only when its resolution check passes — not on vibes.

8. `05-feedback/` — author feedback track (mathematical: a chunk fails and
   triage says the PROOF STEP is suspect, not our transcription).
   - `queries/Q-NNN-*.md` follow the template; each must reproduce WITHOUT
     Lean (sympy numbers or a quoted inference with page ref).
   - Triage rule, lifecycle (OPEN → ANSWERED → RESOLVED), and response-kit
     convention live in `05-feedback/README.md`.
