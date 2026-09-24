# HANDOFF.md — resume point for a fresh session

Read this first, then **AGENTS.md** (updated 2026-09-25 with the one-step
verification loop and F1–F4/S1 classification — those rules govern *how* to
work; this file is just *where things stand*). `README.md` covers the
environment.

Last updated: 2026-09-25 — L7 pilot session closed. L7-FRAG-01 = BLOCKED
on author query Q-001; next session starts a SMALLER lemma (bổ đề 5c/5đ)
per user directive.

---

## One-line status

Docker stack healthy; smoke green; Lemma 7's non-divisibility chunk is
transcribed, step-mapped, sympy-verified, blocked on a real author-facing
sign inconsistency (Q-001), and its batch-written Lean file fails compile #1
with **F2 API errors only** (log saved). Zero author steps are S1 yet.
Start fresh on bổ đề 5c/5đ with the one-step loop.

---

## How to resume (5 minutes to a green smoke)

```bash
# On Windows host, repo root (C:\Users\Anh\Documents\Fermat)
docker compose up -d lean                          # keep it persistent; exec into it
docker compose exec lean sh /workspace/proof/check_env.sh
python pipeline/smoke/smoke_pipeline.py
python pipeline/progress.py --check                # must exit 0
```

Container policy (answered this session): we NEVER spawn/rm per command.
`docker compose up -d lean` starts it once; every compile is
`docker compose exec -T lean sh -c '…'` into the SAME container (observed
Up 3 hours across the session). Named volumes (`lean-elan`, `lake-cache`,
`lake-work`) persist the toolchain and Mathlib oleans across `down`/`up`,
so even a recreate is cheap.

---

## What this session established (evidence, no rework needed)

1. **Smoke/sympy green.** `smoke_pipeline.py` exit 0;
   `04-sympy/test_l7_frag_01.py` exit 0 — n=7: 12 witnesses, n=13: 24,
   **zero** counterexamples to the printed statement.
2. **Transcription triple-verified** (renders `L7_proof_p4a.png`,
   `L7_stmt_p1.png`, `z_stmt_p1.png` + text layer
   `extract_pypdf.txt:1053-1057`): statement/conclusion product is
   `(a^n − b^n)(c^n + a^n)(c^n + b^n)`; the proof's "chứng minh tương tự"
   line lists the three **sums** `b^n+c^n, a^n+b^n, c^n+a^n`. The factor
   `a^n − b^n` is never excluded by the printed chain.
3. **Q-001 filed** (`pipeline/05-feedback/queries/Q-001-product-factor-sign.md`,
   screenshot asset attached, Q-000 template deleted). Classification:
   **F4** — not F1 (our transcription matches the print; the print is
   internally inconsistent). Chunk YAML + `status.tsv` both say BLOCKED.
4. **Normalized step map added** to the chunk YAML (`author_steps:` field,
   S0–S6, one entry per author inference) — satisfies AGENTS preparation
   item 5's second record for L7.
5. **Compile #1 evidence saved**: `pipeline/03-lean/L7-FRAG-01_compile_20260925.log`
   + `MATHLIB_API_LESSONS.md` "Session 2026-09-25" section with all ten
   F2 items and the two falsified recipes CORRECTED (grep-verified against
   pinned Mathlib: `CharP.intCast_eq_zero_iff`,
   `Int.modEq_zero_iff_dvd`, `Int.modEq_iff_dvd`,
   `ZMod.intCast_zmod_eq_zero_iff_dvd` with explicit args).

### Explicit classification (required by AGENTS.md before stopping)

- Process outcome: the whole conclusion path was written in ONE batch and
  compiled once — a violation of the new one-step rule. Recorded, not
  repeated: next session encodes ONE step, compiles, classifies, only then
  continues.
- S0–S5: **F2** (Lean/API representation failures; no mathematical
  rejection). First error line 52. Suspect #1 for the four `Odd.neg_pow`
  pattern failures: prefix `-` vs `^` precedence — see lessons item 1.
- S6 (Tóm lại): **F4** → Q-001 OPEN. Stop rule applies: do not patch,
  do not prove `a^n − b^n` ourselves.
- S1 count: **0**.

---

## Machine & environment facts (durable)

- **Host:** Windows, Docker Desktop, ~8GB RAM cap → `lean` service has
  `mem_limit: 6g`; Docker measures 12 CPUs (service capped `cpus: 10`).
- **`lean` container** (image `fermat-lean:latest`): lean 4.35.0-rc2,
  lake 5.0.0, python3+sympy, git. Toolchain installs once into the
  `lean-elan` volume (NOT baked into the image).
- **Volumes:** `./proof:/workspace/proof` (EDIT-ONLY bind), `lake-work`
  (`/workspace/work`, ALL Lake work), `lean-elan`, `lake-cache`.
- **Compile loop:**
  `docker compose cp <host file> lean:/workspace/work/testproj/…` then
  `docker compose exec -T lean sh -c 'cd /workspace/work/testproj && lake env lean <file>'`.
  `pipeline/` is NOT mounted — use `compose cp`, not the bind.
- **9p freeze pitfall:** NEVER run `lake`/`cache get` inside a Windows
  bind mount (`./proof`, `./proof_verify`). Work happens in
  `/workspace/work` (Linux volume).
- Warm `import Mathlib` compile of the L7 file: ~181 s.
- Mathlib source (container): `/workspace/work/testproj/.lake/packages/mathlib/Mathlib/`.

---

## Where the pipeline stands

Stages in `pipeline/PIPELINE.md`. Verified working: 01-extract (pypdf +
pymupdf, SHA256-pinned), 02-chunks (schema + ledger + YAML; L7 has both
required records now), 03-lean (compiles in container; API lessons live),
04-sympy (L7 test passes), smoke (exit 0), progress.py (exit 0 after this
session's sync), 05-feedback (Q-001 OPEN; template consumed),
BLOCKERS (B-001 RESOLVED).

Chunk states: `L7-FRAG-01` BLOCKED (Q-001). No other chunks exist yet.

---

## Next step (the actual work, user directive 2026-09-25)

**Start with a smaller lemma — bổ đề 5c and bổ đề 5đ** (cited by Lemma
7's proof; formalizing them first also serves L7's `depends_on`):

1. `python pipeline/smoke/smoke_pipeline.py` — green before math.
2. Locate the statements + proofs of bổ đề 5c/5đ in the PDF (search the
   text layer for "bổ đề 5", render those pages at 300 dpi).
3. Create one chunk YAML per lemma with BOTH records:
   literal transcription (signs/exponents/moduli/order preserved) and a
   normalized ordered step map (`author_steps:`) — copy L7-FRAG-01's
   field as the shape reference. If the render is ambiguous, get a second
   visual transcription BEFORE Lean (text layer is navigation only).
4. Sympy-screen any computational claim (cheap, host).
5. One-step loop (AGENTS.md): encode ONE author step → compile →
   classify F1/F2/F3/F4/S1 → only then the next step. Stop on F4.
   - First API lookups: the corrected recipes in
     `MATHLIB_API_LESSONS.md` (batched `#check`, ONE round-trip).
6. On S1 for all steps: `#print axioms` (only Classical.choice,
   propext, quot.sound), update ledger + `progress.py --write`, commit.
7. Then return to L7: set `depends_on`, restart its loop at S0 using the
   step map already in its YAML. Q-001 remains with the author — no
   L7 completion without their sign answer.

---

## Gotchas to not re-learn

- PowerShell ≠ bash: write a script file, exec once; batch container
  round-trips.
- CRLF: `.gitattributes` forces `eol=lf`; never inject `\r`.
- `proof/NameCheck.lean` contents were NEVER executed — its `#check`
  list is untrusted (source of the falsified
  `ZMod.intCast_zmod_eq_zero_iff_dvd` recipe). Batch-check names against
  the pinned local source, then one `lake env lean`.
- Batch-then-compile (what this session did) wastes a full round on
  cascade errors; the one-step rule exists because of exactly this log.
- `lake env lean` with `exact?/apply?/rw?/simp?` is very slow; never run
  two jobs at once.
