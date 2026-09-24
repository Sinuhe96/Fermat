# HANDOFF.md — resume point for a fresh session

Read this first, then **`AGENTS.md`** (the mission and operating rules are
binding). `AGENTS.md` is the source of truth for *how* to work; this file is
just a snapshot of *where things stand*.

Last updated: pilot reset, toolchain + cache verified working.

---

## One-line status

The Docker stack (Lean 4.35.0-rc2 + Mathlib oleans + sympy) is fully
working. The formalization pipeline is scaffolded and smoke-green. **Zero
math has been formalized.** `L7-FRAG-01` is the first chunk and is TODO,
resetting the pilot attempt that violated AGENTS.md.

---

## How to resume (5 minutes to a green smoke)

```bash
# On Windows host, repo root (C:\Users\Anh\Documents\Fermat)
docker compose up -d lean                          # instant if volumes present
docker compose exec lean sh /workspace/proof/check_env.sh   # env ok
python pipeline/smoke/smoke_pipeline.py             # pipeline technically alive
python pipeline/progress.py --check                 # ledger consistent, exit 0
```

If smoke is red → fix the machine first, never the math.

---

## Machine & environment facts (hard-won)

- **Host:** Windows, Docker Desktop, ~8GB RAM cap → `lean` service has
  `mem_limit: 6g`. Docker measured: 12 CPUs.
- **`lean` container** (image `fermat-lean:latest`): lean 4.35.0-rc2,
  lake 5.0.0, python3+sympy 1.11.1, git. Toolchain is NOT baked into the
  image — it installs once into the `lean-elan` volume.
- **Volumes** (compose.yml):
  - `./proof:/workspace/proof` — edit-only host mount (check_env.sh lives here).
  - `lake-work:/workspace/work` — **Linux ext4 volume for ALL Lake work.**
  - `lean-elan:/elan-home` — the Lean toolchain.
  - `lake-cache:/root/.cache` — Mathlib `.ltar` download cache.
- **Running Lake:** a working Mathlib project lives at
  `/workspace/work/testproj` (toolchain `leanprover/lean4:v4.35.0-rc2`,
  mathlib rev from that toolchain). `lake new <name> math` then
  `lake exe cache get` + `lake env lean <file>.lean`.
- **9p freeze pitfall (cost us the most time):** NEVER run `lake`/`cache
  get` inside a Windows bind mount (`./proof`, `./proof_verify`). The 9p
  drvfs filesystem deadlocks the fetch in `D` state (`p9_client_rpc`).
  All Lean compiling happens in `/workspace/work`. Host bind mounts are
  EDIT-ONLY.

---

## Where the pipeline stands

Stages in `pipeline/PIPELINE.md`. Verified working:

- `01-extract` — pypdf + pymupdf, SHA256-pinned supply (`source_manifest.json`),
  per-page `fidelity_check` gate. Pages 1–2 legible for transcription;
  pages 8–29 flagged `MANUAL` (math-dense, cannot auto-trust).
- `02-chunks` — schema (`schema.md`), ledger (`status.tsv`), chunk YAMLs
  (`chunks/`). `L7-FRAG-01` = Todo (reset).
- `03-lean` — `Main.lean` imports `Pilot.Basic` + `Common.Basic`. Both are
  statement-shape scaffolds, currently `sorry` (reset state).
- `04-sympy` — `test_l7_frag_01.py` (L7 hypotheses) passes: 12 witness
  triples at n=7, 24 at n=13, **zero counterexamples**.
- `smoke` — `smoke_pipeline.py` exit 0.
- `progress.py` — dashboard + consistency check, exit 0.
- `BLOCKERS.md` — **B-001 resolved** (Mathlib oleans via Linux volume).
- `05-feedback` — author-feedback triage/format ready; 0 open queries.
- Docker rebuild policy — stable-to-volatile layering, ~250-byte context,
  layer cache in `.buildcache/`. No-change rebuild ~1s; edits have flow chart
  in README.md. Never build from scratch.

---

## Next step (the actual work)

Transcribe **Lemma 7's proof steps** (PDF pp1–2) into chunk `L7-FRAG-01`,
following AGENTS.md exactly:

1. From the PDF renders (re-render at 300dpi: Lemma 7 statement is p1
   bottom, its proof continues p2 top), capture the AUTHOR's hypotheses AND
   deductive steps in order — not just the conclusion.
2. Freeze the chunk's statement **and** proof steps in the YAML.
3. Sympy smoke (already passes) re-confirms no numeric counterexample.
4. Encode the author's chain as Lean steps in `03-lean/Pilot/Basic.lean`.
5. `lake env lean` in `/workspace/work` — Lean certifies the chain or
   exposes the first failing step. A faithful step Lean rejects = a finding
   for the author (`05-feedback`), never a silent fix.
6. Mark DONE, regenerate `PROGRESS.md`, commit.

Render helper (host python, pymupdf available):
```python
import fitz
doc = fitz.open("PROOF_of_FERMAT.pdf")
page = doc[0]                      # index 0 = pdf page 1
clip = fitz.Rect(0, page.rect.height*0.78, page.rect.width, page.rect.height)
page.get_pixmap(dpi=300, clip=clip).save("pipeline/01-extract/out/p1_bot.png")
```

---

## Gotchas to not re-learn

- PowerShell ≠ bash: `cat <<EOF`, `&&`, `| tail` fail in the PS tool. Write
  a script file, exec once; batch container round-trips into one script.
- CRLF: `.gitattributes` forces `eol=lf`. Don't write Linux scripts via
  Windows tools that append `\r` (broke the entrypoint shebang once).
- Batch Mathlib name-checks into ONE `lake env lean` script, not one
  round-trip per lemma.
- YOLO mode is a Shift+Tab / `--yolo` flag on the CLI, not something the
  agent can toggle; if a session is locked down, that's a human action.