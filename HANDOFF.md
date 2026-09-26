# HANDOFF.md — resume point for a fresh session

Read this first, then **AGENTS.md**. Its mandatory fresh-session bootstrap
requires skill discovery/activation and infrastructure readiness before any
chunk or mathematics work; those rules govern *how* to work, while this file
records *where things stand*. `README.md` is the runtime command reference.

Last updated: 2026-09-26 (sixth session) — **`L3-01` DONE** (bổ đề 3:
statement p. 1 §A, proof p. 2 §3). All author steps S0–S11 encoded
one-at-a-time and classified: every step **S1**, assembly `L3.L3_bo_de_3`;
final compile EXIT:0, zero warnings, zero `sorry`, `#print axioms` on all
eight declarations = `[propext, Classical.choice, Quot.sound]`. Three F2
rounds, all tactic-shape (two of them the *same* trap: `rw` on
`a = …`/`c = …` rewrites **inside** the `Int.gcd a c` argument — fixed
with `calc` / `conv_lhs`; one `mul_assoc` direction), plus one
linter-naming round — of 11 compile round-trips in total.
Sympy screen PASS on **real instances** (2184 structured + 2264 boxed,
n ∈ {1,3,5,7,11,13}) — unlike L1/L2/L7 the hypotheses are satisfiable;
the even-n counterexample shows the author's oddness hypothesis is
load-bearing. Docs: `ENCODING_MAP.md` §B L3-01 (patterns P8–P11) and
`MATHLIB_API_LESSONS.md` § Session 2026-09-26. **`L4-01` (bổ đề 4) is
IN_PROGRESS from a parallel session**: its `depends_on: [L3-01]` edge is
now set, and its Lean lane (not started) should reuse `L3.L3_bo_de_3`.
Prior session (fifth, 2026-09-26) — **vision→LaTeX extraction
stage COMPLETE** (commit `9cb73f8`): `regions.py` gates + `regions/pNNN.yml`
records for **all 33 pages REVIEWED** (`regions.py status --pages 33`
exit 0 = the two-phase switch), chunk evidence gate extended with
`regions:` refs (schema criteria 6–8, `progress.py --check` exit 0),
review HTML carries every region's LaTeX with flags, 49 tests green.
Field finding fixed + regression-tested: pymupdf encodes Symbol-font
superscript digits as PUA `U+F030+k` (pp. 16/18/19/22/25/26/29/30).
Human review of `out/review/` (user step) — edits after signoff flip
records to stale; re-`verify` + `signoff` closes them.
Prior session (2026-09-25): **L2-01 DONE**:
bổ đề 2 (statement p. 1, proof p. 2) verified end-to-end via the
contrapositive (power identity `(u^k)^n = u^(k·n)` + assembly), all
author steps S1, compiles EXIT:0 with only the permitted axioms, sympy
screen PASS (3644 real witnesses at n = 1). L1-01 remains DONE.
L7-FRAG-01 = BLOCKED on author query Q-001. Next: another small lemma
(bổ đề 5c/5đ per the earlier directive, or bổ đề 3 in source order).

Concurrent session (2026-09-26, transcription only, stopped before the Lean
lane): **`L4-01` transcription frozen** — bổ đề 4 (statement p. 1, proof
p. 2 §4) transcribed into `02-chunks/chunks/L4-01.yml` with both records
(literal `source_text` + ordered step map S0–S7), evidence bound to the
current extraction run (pages 1 OK / 2 MANUAL → `PASS_WITH_MANUAL`;
`page-00{1,2}-300dpi-full.png`). Screen `04-sympy/test_l4_01.py` PASS on
REAL witnesses (252 inference + 836 parametrisation), with two red-flag
checks that the author's side hypotheses are load-bearing (m prime in S2;
m ∤ h·l·r in S5). Status IN_PROGRESS: **no Lean work done** — `lean_decls`
is empty and no step has an F1–F4/S1 classification. L4's S6 cites bổ đề 3
("áp dụng bổ đề 3"), so L4-01 must gain `depends_on: [L3-01]` once L3-01 is
DONE, and the Lean lane must import bổ đề 3 rather than re-derive it.
Capability note: that session had NO vision (image reads return binary, the
repo vision-probe included), so the render read for the transcription is the
human-signed REVIEWED region LaTeX (p1 R2/R3, p2 R2), cross-checked against
both engine text layers — not a fresh independent vision pass. A second
session is transcribing bổ đề 3 (`L3-01`, TODO) in parallel; `status.tsv`,
`PROGRESS.md` and this file are shared write targets between the two.

---

## One-line status

Docker stack healthy; smoke green. **`L3-01` DONE, `L2-01` DONE,
`L1-01` DONE** — three lemmas fully verified with the one-step loop (one
named Lean declaration per author step, final compile EXIT:0, `#print
axioms` = [propext, Classical.choice, Quot.sound] only). `L3-01`'s sympy
screen is the first **instance-based** one (`04-sympy/test_l3_01.py`:
2184 structured + 2264 boxed real instances, n ∈ {1,3,5,7,11,13});
L1/L2's screens are inference-only because their hypotheses (the FLT
equation) are unsatisfiable for n ≥ 3. **`L4-01` (bổ đề 4)
IN_PROGRESS** — transcription, step map S0–S7, sympy screen and evidence
block are done (parallel session); its Lean lane is not started and now
carries `depends_on: [L3-01]`.
Lemma 7's non-divisibility chunk stays transcribed, step-mapped,
sympy-verified and BLOCKED on the author-facing sign inconsistency
Q-001; its flat-copy Lean file still has F2 errors plus one `sorry`
marking that gap, and zero L7 author steps are S1.

---

## Mandatory fresh-session bootstrap

After reading this file and `AGENTS.md`, identify the active agent harness
and use its native skill discovery/loading mechanism. Command Code examples
include `/skills` and `cmdc skills list --debug`; in OMP, use `skill://<name>`
for exposed skills and read repository-local skill files directly. Do not run
`cmdc` unless using Command Code. If a required skill is not exposed by the
loader, read its canonical file directly; if unavailable, report the missing
prerequisite before work. Normal Lean work requires `lean4` and the Fermat
overlay before starting the container or doing any Lean/Lake work.

```powershell
# On Windows host, repo root
# Skill discovery/loading happens through the agent harness, not this shell.
docker compose up -d lean
docker compose exec -T lean sh /workspace/proof/check_env.sh
docker compose exec -T lean python /workspace/pipeline/progress.py --check
```

Do not begin chunk work until all gates are green. The default readiness check
is fast and compile-free. After image, toolchain, cache, or workspace changes,
run `check_env.sh --full` once to compile `import Mathlib`.

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

## What the L2 session established (evidence, no rework needed)

1. **Chunk `L2-01` DONE** (`pipeline/02-chunks/chunks/L2-01.yml`,
   `status.tsv`, `PROGRESS.md`): bổ đề 2 — statement p. 1 + proof p. 2 §2
   transcribed from fresh 300 dpi full-page renders
   (`01-extract/out/page-001-300dpi-full.png`,
   `page-002-300dpi-full.png`); statement, proof, and the exponent
   spellings `nk₀`/`k₀`/`ℕ*` confirmed by two reads (render + pypdf text
   layer, verbatim agreement). Step map S0–S3: assume a nonzero solution
   of the nk₀-equation (S0), power identity `(uᵏ)ⁿ = u^{k·n}` (S1),
   lifted solution of the n-equation (S2), contradiction/contrapositive
   (S3).
2. **Lean: one declaration per author step, all S1** —
   `L2_step_S1` (S0+S1+S2: nonzero solution of `x^{k·n}+…` lifts to
   `(uᵏ,vᵏ,tᵏ)` of `xⁿ+…`) and the assembly `L2_bo_de_2` (S3,
   contrapositive wrap). Final compile EXIT:0, no `sorry`, no warnings
   (`_hn`/`_hk` for the carried-but-unused hypotheses); `#print axioms`
   on both = propext, Classical.choice, Quot.sound. Log:
   `03-lean/L2-01_compile_20260925.log` (sha256 of the compiled copy
   recorded).
3. **Sympy screen PASS** (`04-sympy/test_l2_01.py`): identity screened on
   1000 (n,k,u) cases; the lift is exercised on **3644 real witnesses**
   by taking n = 1 (the transformation does not depend on n); vacuity on
   {5,7,11,13} × k ∈ {2,3,5}: 0 candidates as expected — for n ≥ 3 the
   hypotheses admit no witness, so screens test inferences, not witnesses.
4. **One F2 round, no F1/F3/F4:** `rw [← pow_mul]` failed — pin
   signature is `pow_mul : a ^ (m * n) = (a ^ m) ^ n`
   (`Mathlib/Algebra/Group/Pow/Monoid.lean:459`), direction
   `rw [pow_mul]`. Lesson + a direction table folded into
   `MATHLIB_API_LESSONS.md`; proof pattern **P7** and the L2-01 §B table
   in `ENCODING_MAP.md`.
5. **Docs updated**: ENCODING_MAP §B Chunk L2-01 (step table, reusable
   results, P7, method note); MATHLIB_API_LESSONS session entry;
   PROGRESS.md regenerated (2/3 DONE); HANDOFF.md (this file).
6. **Evidence renders on disk**: `page-001-300dpi-full.png` /
   `page-002-300dpi-full.png` + `.json` provenance in
   `01-extract/out/` (same on-disk status as the L1 renders — evidence
   PNGs are not tracked in git).

## What the L3 session established (evidence, no rework needed)

1. **Chunk `L3-01` DONE** (`pipeline/02-chunks/chunks/L3-01.yml`,
   `status.tsv`, `PROGRESS.md`): bổ đề 3 — statement p. 1 §A, proof
   p. 2 §3 — transcribed from the signed REVIEWED region records
   (`01-extract/regions/p001.yml` R2, `p002.yml` R1–R2) and re-read
   visually from the 300 dpi crops (`page-001-300dpi-region-02.png`,
   `page-002-300dpi-region-01/02.png`); three reads agree, including the
   contested connective `; vì` at p2 R2 line 1 (a first vision pass
   misread it as `và`; zoom read + text layer + reviewed record all give
   `vì`, the `vì … nên` correlative). Step map S0–S11 in the chunk YAML.
2. **Lean: one declaration per author step, all S1** —
   `L3_step_S0`, `L3_step_S1_S2`, `L3_step_S3_S4`, `L3_step_S5`,
   `L3_step_S6_S8`, `L3_step_S9_S10`, `L3_step_S11`, plus the assembly
   `L3_bo_de_3` (`03-lean/L3/Basic.lean`). Final compile EXIT:0, no
   `sorry`, no warnings; `#print axioms` on all eight = propext,
   Classical.choice, Quot.sound. Log:
   `03-lean/L3-01_compile_20260926.log` (11 rounds kept as evidence).
3. **Sympy screen PASS on real instances** (`04-sympy/test_l3_01.py`):
   the whole S0–S11 chain plus the statement's witness construction on
   2184 structured + 2264 boxed instances (n ∈ {1,3,5,7,11,13}); the
   even-n counterexample (a = -4, b = -9, c = 6, n = 2) exhibits that the
   author's oddness hypothesis is load-bearing. New method note: when a
   lemma's hypotheses *are* satisfiable, use an instance-based screen
   instead of the L1/L2/L7 vacuity note.
4. **Formal additions were side conditions only** — c'_1 ≠ 0 (divides
   the nonzero a) for the S2 cancellation, c'_2 ≠ 0 (from c = c'_1·c'_2)
   so that k ≠ 0 at S4, 1 ≤ n for `c'_1^n = c'_1·c'_1^{n-1}` (S2) and
   `k ∣ k^n` (S7), and `Odd n`/`0 < n` as two binders of the paper's
   "n là số nguyên dương lẻ" (the oddness is used only at S11 via
   `(-1)^n = -1`).
5. **Two reusable API lessons + one trap** (`MATHLIB_API_LESSONS.md`
   § Session 2026-09-26): `Int.exists_gcd_one` does S0 in one shot;
   `Int.isCoprime_iff_gcd_eq_one` bridges to `IsCoprime` so that
   `IsCoprime.dvd_of_dvd_mul_left` (Euclid) and `IsCoprime.pow` do S4/S9;
   and the trap that cost two rounds — **`rw` with `h : a = …` (or
   `c = …`) rewrites inside the `Int.gcd a c` argument of the goal**, so
   use `calc` or `conv_lhs`/`conv_rhs`. Patterns P8–P11 and the
   step→declaration table: `ENCODING_MAP.md` §B Chunk L3-01.
6. **Downstream integration:** `L4-01` (bổ đề 4, a parallel session's
   transcription) cites bổ đề 3 at its S6; its `depends_on: [L3-01]` is
   now declared (the chunk's own note asked for this once bổ đề 3
   existed), and its Lean lane must reuse `L3.L3_bo_de_3` — module
   wiring (`[[lean_lib]] name = "L3"`) is still pending per
   `ENCODING_MAP.md` §A.

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
- **`lean` container** (image `fermat-lean:latest`): Lean 4.35.0-rc2,
  Lake 5.0.0, pinned pypdf/PyMuPDF/Sympy, `rg`, and git. The separate local
  `leanprovercommunity/lean` image is unused. The toolchain installs once
  into `lean-elan` (not baked into the image).
- **Mounts:** `./proof:/workspace/proof`, `./pipeline:/workspace/pipeline`,
  read-only PDF at `/workspace/source/PROOF_of_FERMAT.pdf`, plus `lake-work`
  (`/workspace/work`, ALL Lake work), `lean-elan`, and `lake-cache`.
- **Compile loop:**
  `docker compose exec -T lean sh /workspace/proof/compile_lean.sh <path-under-03-lean>`.
  The wrapper copies from the pipeline bind mount into the Linux Lake volume
  before invoking `lake env lean`.
- **9p freeze pitfall:** NEVER run `lake`/`cache get` inside a Windows
  bind mount (`./proof`, `./pipeline`, or `./proof_verify`). Work happens in
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
pymupdf, SHA256-pinned), 02-chunks (schema + ledger + YAML; all existing
chunks have both required records), 03-lean (compiles in container; API
lessons + encoding map live), 04-sympy (L1 + L2 + L3 + L4 + L7 screens all
PASS — re-run together after L3-01), smoke (exit 0), progress.py (exit 0),
05-feedback (Q-001 OPEN), BLOCKERS (B-001 RESOLVED).

Chunk states: `L3-01` DONE (bổ đề 3, gcd-splitting of a·b = c^n, steps
S0–S11 all S1, assembly `L3_bo_de_3`); `L2-01` DONE (bổ đề 2,
contrapositive power-lift, assembly `L2_bo_de_2`); `L1-01` DONE (bổ đề 1,
six steps S1, assembly `L1_bo_de_1`); `L4-01` IN_PROGRESS (bổ đề 4 —
transcription, step map S0–S7, sympy screen and evidence block complete
from a parallel session; Lean lane not started; `depends_on: [L3-01]`);
`L7-FRAG-01` BLOCKED (Q-001). Five chunks exist: 3 DONE / 1 IN_PROGRESS /
1 BLOCKED.

Reuse: L1/L2/L3 are **not** wired as Lean modules yet — deferred by user
decision to the first real consumers. That consumer now exists: `L4-01`
declares `depends_on: [L3-01]`, so its Lean lane is the first chunk that
must import/reuse a DONE chunk's declarations (`L3.L3_bo_de_3`, or its
step lemmas) instead of re-deriving them; the p. 6 main theorem (bổ đề 1)
and bổ đề 6 remain the other consumers. Rule + wiring recipe + the
volume-only `Pilot` lean_lib reproducibility gap:
`pipeline/03-lean/ENCODING_MAP.md` §A "Reusing a DONE chunk".

Workflow hardening (2026-09-25, same day): the extraction-stage
fidelity gate is now **consumed per chunk** — every chunk carries an
evidence block (`source_pdf_sha`, `extract_run_sha`, `fidelity`,
`renders`, `lean_decls`) and `progress.py --check` machine-verifies it
for DONE chunks (extraction binding, page verdicts, render provenance,
declarations present in the Lean file, no `sorry`). All three chunks are
backfilled; the check was proven to fail on tampered evidence. Schema:
`02-chunks/schema.md` criteria 6–7.

Vision→LaTeX stage (2026-09-26, commit `9cb73f8`): the implicit
transcription step is now a named stage, tool-gated end to end
(`pipeline/01-extract/regions.py`: `precheck` → `words` → `plan` →
vision crop reads → `verify` → `signoff`; `PIPELINE.md` stage 1
documents it). All 33 page records REVIEWED with fresh signoffs; chunks
L1-01/L2-01/L7-FRAG-01 carry `regions:` refs; schema criterion 8 +
`progress.py check_evidence` enforce page records (REVIEWED, fresh,
sha-bound) for every DONE chunk — proven to fail on `not REVIEWED` and
`signoff stale` tampering. Digit audit caught three real classes during
backfill: vision `s`→`5` misread (p14, text-layer + F-block notation
settled it), PUA-encoded superscript digits (tool fixed +
`test_pua_encoded_superscript_digits_counted`), and a page-total sort
bug (fixed). `out/review/` shows per-region LaTeX + flags for the
human edit pass (KaTeX embedding deferred by decision; copy buttons +
`regions.py export` serve external editors).

---

## Next step (the actual work)

**The vision phase is done** (`regions.py status --pages 33` exit 0):
the text-only Lean phase may resume — provided the human edit pass over
`out/review/` is accepted (or skipped by user decision; any edit flips
the page to `STALE`, then `regions.py verify` + `signoff` re-close it).

**L2-01 and L3-01 are closed.** Candidates, in the order the repo's own
records point at them:

1. **`L4-01` (bổ đề 4), Lean lane** — a parallel session already froze its
   transcription, step map S0–S7, sympy screen and evidence block; the
   Lean lane is untouched (`lean_decls:` empty, no F1–F4/S1 assigned). It
   declares `depends_on: [L3-01]` because its S6 applies bổ đề 3, so it is
   also the first chunk that must **wire and reuse** a DONE chunk
   (`ENCODING_MAP.md` §A "Reusing a DONE chunk": `[[lean_lib]] name = "L3"`
   + `import`), rather than re-deriving bổ đề 3.
2. **bổ đề 5c / 5đ** (user directive 2026-09-25; cited by Lemma 7's proof),
   or **bổ đề 5 a) b)** (p. 1 §A, cited by the same chain).
3. **bổ đề 5 in source order** / bổ đề 6 — bổ đề 6 is bổ đề 1's second
   consumer (`(u,v) = (u,t) = (v,t) = 1` as a hypothesis).

Whichever is chosen, confirm the statement + proof against a 300 dpi
render (the reviewed region records are the authoritative transcription;
the text layer is navigation only).

Follow AGENTS.md exactly:

1. **Load the Lean skill first** (mandatory gate: `SKILL.md` +
   `references/*` + `MATHLIB_API_LESSONS.md` + `ENCODING_MAP.md`).
2. `docker compose exec -T lean sh /workspace/proof/check_env.sh` — green before math.
3. Locate the statement + proof in the PDF: use the REVIEWED region
   records (`01-extract/regions/pNNN.yml`); re-read the 300 dpi crops if
   anything is ambiguous.
4. Create the chunk YAML with BOTH records — L1-01 is the shape reference
   for `author_steps:`, L3-01 for the full classification block.
5. Sympy-screen the *inferences*; if the lemma's hypotheses are
   satisfiable (as bổ đề 3/4 are), screen **real instances** instead of
   writing a vacuity note (`ENCODING_MAP.md` §B L3-01 method note).
6. One-step loop: encode ONE author step → compile → classify
   F1/F2/F3/F4/S1 → only then continue. Stop on F4 and file a query.
   Watch L3's two F2 traps: `rw` on `a = …`/`c = …` rewrites inside
   `Int.gcd a c` (use `calc`/`conv_*`), and `mul_assoc` reassociates
   *leftwards* (`← mul_assoc` to expose `a * b`).
7. On S1 for all steps: `#print axioms`, update ledger +
   `progress.py --write PROGRESS.md`, commit.
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
- Search the pinned Mathlib source with `rg` before guessing a name: free and
  exact, whereas a wrong guess costs a 300+ s round-trip.
