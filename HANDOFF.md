# HANDOFF.md — resume point for a fresh session

Read this first, then **AGENTS.md** (updated 2026-09-25 with the one-step
verification loop and F1–F4/S1 classification, and with the mandatory
Lean-skill gate — those rules govern *how* to work; this file is just
*where things stand*). `README.md` covers the environment.

Last updated: 2026-09-25 (second session, same day) — **L1-01 is DONE**:
bổ đề 1 (statement p. 1, proof p. 2) verified end-to-end, all six author
steps S1. L7-FRAG-01 = BLOCKED on author query Q-001. Next: another small
lemma (bổ đề 5c/5đ per the earlier directive, or bổ đề 2 in source order).

---

## One-line status

Docker stack healthy; smoke green. **`L1-01` DONE** — bổ đề 1 verified with
the one-step loop, one named Lean declaration per author step
(`03-lean/L1/Basic.lean`), final compile EXIT:0, `#print axioms` =
[propext, Classical.choice, Quot.sound] only, sympy screen PASS
(`04-sympy/test_l1_01.py`). Zero F1/F3/F4 outcomes: every author step was
accepted as written. Lemma 7's non-divisibility chunk stays transcribed,
step-mapped, sympy-verified and BLOCKED on the author-facing sign
inconsistency Q-001; its flat-copy Lean file still has F2 errors plus one
`sorry` marking that gap, and zero L7 author steps are S1.

---

## How to resume (5 minutes to a green smoke)

```bash
# On Windows host, repo root (C:\Users\Anh\Documents\Fermat)
docker compose up -d lean                          # keep it persistent; exec into it
docker compose exec lean sh /workspace/proof/check_env.sh
python pipeline/smoke/smoke_pipeline.py
python pipeline/progress.py --check                # must exit 0
```

Container policy (answered 2026-09-25): we NEVER spawn/rm per command.
`docker compose up -d lean` starts it once; every compile is
`docker compose exec -T lean sh -c '…'` into the SAME container (observed
Up 4+ hours across sessions). Named volumes (`lean-elan`, `lake-cache`,
`lake-work`) persist the toolchain and Mathlib oleans across `down`/`up`,
so even a recreate is cheap.

---

## What the L1 session established (evidence, no rework needed)

1. **Chunk `L1-01` DONE** (`pipeline/02-chunks/chunks/L1-01.yml`,
   `status.tsv`, `PROGRESS.md`): statement p. 1 + proof p. 2 transcribed
   and step-mapped S0–S6 from the 300 dpi renders
   (`01-extract/out/L1_p1_300dpi.png`, `L1_p2_300dpi.png`), divisibility
   direction and the `(1'')` label confirmed by a second visual read.
2. **Lean: one declaration per author step, all S1** —
   `L1_reduce_coprime`, `L1_step_S2_S3`, `L1_step_S4`, `L1_step_S5`,
   `L1_step_S6`, plus the assembly `L1_bo_de_1`. Final compile EXIT:0, no
   `sorry`, no warnings; `#print axioms` on all six = propext,
   Classical.choice, Quot.sound. Log:
   `03-lean/L1-01_compile_20260925.log`.
3. **Sympy screen PASS** (`04-sympy/test_l1_01.py`): every inference
   screened (S1 216000 triples, S2+S3 on the 6472 solutions that exist for
   n = 1,2, S4 16000 cases, S5/S6 12674 triples). Method note: for n ≥ 3
   the hypothesis has **no** witnesses, so the screen tests inferences,
   not witnesses.
4. **Formal additions were side conditions only** — S0+S1 needs `d ≠ 0`
   and cancellation by `dⁿ ≠ 0`; S4 needs `n ≠ 0` (false for n = 0),
   supplied from the author's `n ≥ 3`; S6's "chứng minh tương tự" had to be
   spelled out (the third coordinate comes by *subtraction*, not by the sum
   used for (u,v)).
5. **Reuse layer added**: `03-lean/ENCODING_MAP.md` (author notation →
   Lean terms, per-chunk step tables, compiled proof patterns P1–P6) is now
   the companion to `MATHLIB_API_LESSONS.md`; both are part of AGENTS.md's
   mandatory preparation gate. Lessons file gained 17 pin-verified items.

### Prior session (L7 pilot) — still stands

1. **Smoke/sympy green.** `04-sympy/test_l7_frag_01.py` exit 0 — n=7: 12
   witnesses, n=13: 24, **zero** counterexamples to the printed statement.
2. **Transcription triple-verified** (renders `L7_proof_p4a.png`,
   `L7_stmt_p1.png`, `z_stmt_p1.png` + text layer
   `extract_pypdf.txt:1053-1057`): statement/conclusion product is
   `(a^n − b^n)(c^n + a^n)(c^n + b^n)`; the proof's "chứng minh tương tự"
   line lists the three **sums** `b^n+c^n, a^n+b^n, c^n+a^n`. The factor
   `a^n − b^n` is never excluded by the printed chain.
3. **Q-001 filed** (`pipeline/05-feedback/queries/Q-001-product-factor-sign.md`,
   screenshot asset attached). Classification: **F4** — not F1 (our
   transcription matches the print; the print is internally inconsistent).
4. **Normalized step map** in the L7 chunk YAML (`author_steps:`, S0–S6).
5. **Compile #1 evidence saved**: `03-lean/L7-FRAG-01_compile_20260925.log`
   — S0–S5 **F2** (representation only), S6 **F4** (Q-001), S1 count 0.
   Process violation recorded: the whole path was written in one batch;
   the L1 session used the one-step loop instead and hit no such cascade.

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
- Warm `import Mathlib` compile: ~181 s (L7 file, first session) but
  **288–387 s** measured for `L1/Basic.lean` under load — plan one
  compile per author step, not per name.
- Mathlib source (container): `/workspace/work/testproj/.lake/packages/mathlib/Mathlib/`.
- Host-side pinned source for greps (read-only):
  `proof_verify/.lake/packages/mathlib/Mathlib/`.

---

## Where the pipeline stands

Stages in `pipeline/PIPELINE.md`. Verified working: 01-extract (pypdf +
pymupdf, SHA256-pinned), 02-chunks (schema + ledger + YAML; both existing
chunks have both required records), 03-lean (compiles in container; API
lessons + encoding map live), 04-sympy (L1 + L7 tests pass), smoke
(exit 0), progress.py (exit 0), 05-feedback (Q-001 OPEN),
BLOCKERS (B-001 RESOLVED).

Chunk states: `L1-01` DONE (bổ đề 1, six steps S1, assembly
`L1_bo_de_1`); `L7-FRAG-01` BLOCKED (Q-001). Two chunks exist.

Reuse: L1 is **not** wired as a Lean module yet — deferred by user
decision to its first real consumer (p. 6 main theorem "áp dụng bổ đề 1",
or bổ đề 6). Rule + wiring recipe + the volume-only `Pilot` lean_lib
reproducibility gap: `pipeline/03-lean/ENCODING_MAP.md` §A "Reusing a DONE
chunk".

---

## Next step (the actual work)

**L1-01 is closed; pick the next lemma.** Two candidates, both with
satisfied dependencies:

- **bổ đề 5c / 5đ** (user directive 2026-09-25; cited by Lemma 7's proof —
  formalizing them first also serves L7's `depends_on`), or
- **bổ đề 2** (p. 1, next in source order). Navigation text only, from the
  extract layer: reads roughly as "with `n ≥ 3`, if `xⁿ + yⁿ = zⁿ` has no
  nonzero integer solution then for every `k` neither does
  `x^{nk} + y^{nk} = z^{nk}`" — **not a transcription**; the text layer is
  navigation only, so confirm against a 300 dpi render before freezing the
  chunk. (Its proof, p. 2, runs the contrapositive.)

Either way, follow AGENTS.md exactly:

1. **Load the Lean skill first** (mandatory gate: `SKILL.md` +
   `references/*` + `MATHLIB_API_LESSONS.md` + `ENCODING_MAP.md`).
2. `python pipeline/smoke/smoke_pipeline.py` — green before math.
3. Locate the statement + proof in the PDF: search the text layer, render
   those pages at 300 dpi, transcribe literally (two visual reads if
   ambiguous; the text layer is navigation only).
4. Create the chunk YAML with BOTH records — L1-01 is the shape reference
   for `author_steps:`.
5. Sympy-screen the *inferences*, not witnesses (see ENCODING_MAP §B
   method note: for n ≥ 3 the hypothesis is unsatisfiable).
6. One-step loop: encode ONE author step → compile → classify
   F1/F2/F3/F4/S1 → only then continue. Stop on F4 and file a query.
7. On S1 for all steps: `#print axioms`, update ledger +
   `progress.py --write`, commit.
8. Then L7: set `depends_on`, restart its loop at S0 from its existing
   step map. Q-001 stays with the author — no L7 completion without their
   sign answer.

---

## Gotchas to not re-learn

- PowerShell ≠ bash: write a script file, exec once; batch container
  round-trips.
- CRLF: `.gitattributes` forces `eol=lf`; never inject `\r`.
- `proof/NameCheck.lean` contents were NEVER executed — its `#check`
  list is untrusted (source of the falsified
  `ZMod.intCast_zmod_eq_zero_iff_dvd` recipe). Batch-check names against
  the pinned local source, then one `lake env lean`.
- Batch-then-compile wastes a full round on cascade errors; the one-step
  rule exists because of exactly that log.
- `lake env lean` with `exact?/apply?/rw?/simp?` is very slow; never run
  two jobs at once.
- Grep the pinned Mathlib source locally before guessing a name: free and
  exact, whereas a wrong guess costs a 300+ s round-trip.
