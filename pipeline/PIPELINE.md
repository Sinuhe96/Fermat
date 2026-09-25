# Pipeline: PDF -> faithful text -> lemma chunks -> Lean

Stages:

1. `01-extract/` — PDF extraction and source rendering, deterministic and reproducible.
   - `extract.py` runs pypdf AND PyMuPDF and writes both transcripts; use
     `--pages` only for bounded checks, not as a replacement for full extraction.
   - `render_pdf.py` renders a one-based page or crop to RGB PNG and records
     source/output hashes, geometry, DPI, and tool version in sidecar JSON.
   - `fidelity_check.py` decides, per page, whether the text layer may be
     transcribed from (OK) or the render must be used instead (MANUAL).
     Metrics (NFC-normalized): token-stream SequenceMatcher (order-aware
     verdict driver), digit-stream agreement (any digit disagreement
     escalates: digits are load-bearing for Lean), measured math-density
     routing (no hardcoded page-range guess). Non-OK pages carry
     actionables: preferred engine, first divergent token windows with
     context, and unique-token samples per engine. Transcript sha256 pins
     the exact bytes the verdicts were computed on. The pipeline STOPS
     here if fidelity fails. The gate is consumed per chunk: every chunk's
     evidence block binds it to one extraction run (`source_pdf_sha`,
     `extract_run_sha`, `fidelity`, `renders`), and `progress.py --check`
     validates that binding.
   - Why two tools: math-dense pages extract differently per engine.
     Divergence CONFIRMS unreliability — the two extracts agreeing is the
     signal; the per-page diff pinpoints which spans need eyes.
   - Math pages that fail are routed to MANUAL transcription from the rendered

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

5. `smoke/` — container readiness checks (NOT math verification).
   - Fast mode hard-fails on wrong/missing tools or Python pins, bad mounts,
     missing Lake/Mathlib state, or page-1 extraction/rendering failure. It
     deliberately does not compile Mathlib.
   - `--full` additionally compiles a temporary `import Mathlib` theorem in
     `/workspace/work/testproj`; use it after image, toolchain, cache, or
     workspace changes.
   - Run through `docker compose exec -T lean sh /workspace/proof/check_env.sh`
     before large work. Python may use `/workspace/pipeline`; Lake never may.

6. `progress.py` + `PROGRESS.md` — where are we, right now.
   - `python pipeline/progress.py --check` prints the dashboard and verifies
     ledger consistency (tsv vs chunk files, unknown deps, cycles). Exit 1
     means the TRACKING is broken — fix it before trusting the picture.
     `--check` also machine-verifies each DONE chunk's evidence block
     (extraction binding, page verdicts, render provenance, `lean_decls` vs
     the Lean file, no `sorry`).
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
