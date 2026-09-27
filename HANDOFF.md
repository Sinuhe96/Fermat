# HANDOFF.md — resume point for a fresh session

Read this first, then **AGENTS.md** (binding rules, mandatory bootstrap, the
one-step verification loop, the F1–F4/S1 outcome classes) and **README.md**
(runtime commands, container policy, mount table). This file records *where
things stand* and deliberately does not repeat what those two say.

Last updated: 2026-09-28 (**twelfth session**): **bổ đề 7 is complete.**
`L7-FRAG-02` … `L7-FRAG-06` (its remaining conclusion groups) and the thin
section assembly `L7-ASM` are **DONE**: the assembly's `L7_bo_de_7` in
`03-lean/L7ASM/Basic.lean` returns the lemma's full printed conclusion list in
the numbered forms the main proof cites — the non-divisibility product,
(a)/(b)/(c)/(d), (18), (19), (20), (21), (22), (22') and `n ≡ 1 (mod 6)`.
Six new chunks, 26 declarations, about 28 container rounds — of which only
~10 carried real errors and **every one was F2** (encoding/API; some siblings
were cascade failures, a leaf's olean missing after an earlier failed round in
the same chain). There is **no F1/F4** anywhere in this lane. Two items are recorded in
`05-feedback/queries/Q-002-under-printed-steps.md` as **EDITORIAL, not
blocking** (F3): the printed p. 5 proof never derives (22) although the
statement list prints it and p. 30 R2 consumes it, and one underlined line of
the `n ≡ −1 (mod 6)` reductio is printed at modulus `n` where the argument
needs `n²`. So: **all thirteen chunks are DONE**, none BLOCKED, and no query is
OPEN. The remaining verification work is the **main proof (pp. 6–33)** — see
"Next step" below.
---

## Chunk ledger

| chunk | lemma | status | where it lives (under `pipeline/`) |
|---|---|---|---|
| `L1-01` | bổ đề 1 | DONE | `03-lean/L1/Basic.lean`, assembly `L1_bo_de_1`, log `03-lean/L1-01_compile_20260925.log` |
| `L2-01` | bổ đề 2 | DONE | `03-lean/L2/Basic.lean`, `L2_bo_de_2`, log `03-lean/L2-01_compile_20260925.log` |
| `L3-01` | bổ đề 3 | DONE | `03-lean/L3/Basic.lean`, `L3_bo_de_3`, log `03-lean/L3-01_compile_20260926.log` |
| `L4-01` | bổ đề 4 | DONE | `03-lean/L4/Basic.lean`, `L4_bo_de_4`, log `03-lean/L4-01_compile_20260926.log` |
| `L5-01` | bổ đề 5, parts a)–d) | DONE | `03-lean/L5/Basic.lean`, `L5_bo_de_5`, log `03-lean/L5-01_compile_20260926.log` |
| `L6-01` | bổ đề 6 | DONE | `03-lean/L6/Basic.lean`, `L6_bo_de_6`, log `03-lean/L6-01_compile_20260926.log` |
| `L7-FRAG-01` | bổ đề 7, non-divisibility conclusion | DONE | `03-lean/L7/Basic.lean`, `lean_lib L7`, log `03-lean/L7-FRAG-01_compile_20260926.log` + the 2026-09-27 S5c/S6 round; pre-restart exhibit `03-lean/Pilot/Basic.lean` (frozen, imported by nothing) |
| `L7-FRAG-02` | bổ đề 7, display (a) + the (b)/(c)/(d) toolkit | DONE | `03-lean/L7F2/Basic.lean`, log `03-lean/L7-FRAG-02_compile_2026*.log` |
| `L7-FRAG-03` | bổ đề 7, (19), (20) (the `b^{3n}+c^{3n}` chain + the "Lưu ý" symmetry) | DONE | `03-lean/L7F3/Basic.lean`, log `03-lean/L7-FRAG-03_compile_2026*.log` |
| `L7-FRAG-04` | bổ đề 7, (18) and (22') (the factorization + cancellation) | DONE | `03-lean/L7F4/Basic.lean`, log `03-lean/L7-FRAG-04_compile_20260928.log` |
| `L7-FRAG-05` | bổ đề 7, `n ≡ 1 (mod 6)` | DONE | `03-lean/L7F5/Basic.lean`, log `03-lean/L7-FRAG-05_compile_20260928.log` |
| `L7-FRAG-06` | bổ đề 7, (21) and (22) | DONE | `03-lean/L7F6/Basic.lean`, log `03-lean/L7-FRAG-06_compile_20260928.log` |
| `L7-ASM` | bổ đề 7, section assembly (`L7_bo_de_7`, the main proof's entry point) | DONE | `03-lean/L7ASM/Basic.lean`, logs `03-lean/L7-ASM_compile_20260928.log` + `03-lean/L7-ASM.axioms_20260928.log` |

Every DONE row is machine-verified, not asserted: the chunk YAML's evidence
block (`source_pdf_sha`, `extract_run_sha`, `fidelity`, `renders`, `regions`,
`lean_decls`), `status.tsv` and the regenerated `PROGRESS.md` agree, and
`progress.py --check` exits 0; each Lean file compiles EXIT 0 with zero
warnings, zero `sorry`, and `#print axioms` = propext / Classical.choice /
Quot.sound only, every author step S1 (no F1/F4 anywhere; the few F3
fill-ins per chunk are listed in that chunk's YAML). Per-chunk step tables,
reusable signatures and compiled patterns live in `03-lean/ENCODING_MAP.md` §B
and `03-lean/MATHLIB_API_LESSONS.md` — read those, do not re-derive.

Reuse state: the tracked `03-lean/lakefile.toml` declares `lean_lib` for
`Common` and `L1`–`L7`, `Main.lean` imports them, and every producer's olean is
published, so `import Lk.Basic` resolves in a new chunk (the `Pilot` entry is
gone — that module is a frozen exhibit). Producer edges in
use: `L4-01 → L3-01`; `L6-01 → L3-01 + L4-01 + L5-01`; `L7-FRAG-01 → L5-01`
(the tail reuses `L5_gcd_eq_one_of_not_dvd` for Fermat's little theorem).

Gate status at the twelfth session's close (2026-09-28): `progress.py --check`
exit 0 with **13/13 DONE**, `proof/check_env.sh` SMOKE PASS,
`01-extract/fidelity_check.py out` exit 0 (PASS_WITH_MANUAL, 19 manual pages),
`04-sympy/run_all.py` 13/13 (`04-sympy/run_all_20260928.log`),
`compile_lean.sh L7ASM/Basic.lean` EXIT 0 (zero warnings, zero `sorry`;
`03-lean/L7-ASM_compile_20260928.log`) and the axioms gate
`compile_lean.sh probes/L7-ASM.axioms.lean` EXIT 0: all 26 declarations of this
lane depend only on propext / Classical.choice / Quot.sound (23 on exactly that
set, 3 on a subset) — `03-lean/L7-ASM.axioms_20260928.log`. The aggregate root
`compile_lean.sh Main.lean` (which now imports `L1`–`L7`, `L7F2`–`L7F6`,
`L7ASM`) also exits 0 (`03-lean/Main_20260928.log`) — the "everything
typechecks" gate — so every gate of the DONE recipe is green.

---

## Next step — the main proof (pp. 6–33)

### What is now closed

bổ đề 7 is fully verified and **assembled**: `L7_bo_de_7` (chunk `L7-ASM`)
takes the lemma's three hypotheses and returns every printed conclusion in the
numbered forms the main proof cites. Per-chunk step tables, the reused
signatures and the compiled proof patterns are in `03-lean/ENCODING_MAP.md` §B
("Chunks L7-FRAG-02 … L7-FRAG-06 + L7-ASM") and the API pitfalls that cost the
nine rounds are in `03-lean/MATHLIB_API_LESSONS.md` (the 2026-09-28 session
entry) — read those before writing Lean; the round count there is the evidence
that guessing is expensive at this pin.

Facts a main-proof chunk will need:

- `L5_bo_de_5` conjuncts `.2.2.1` (5c) / `.2.2.2` (5d) are the primitive
  number theory bổ đề 7 needed; `L7F3_five_c` is 5c **without** bổ đề 5's
  coprimality hypothesis (the author's own remark: "(không cần giả thiết
  (u,v) = 1)");
- the two use sites of bổ đề 7 are p. 30 R2 ("Từ (17), (21), (22), ta có …")
  and p. 32 R1 (the cancellation by `a^n b^n (a^n − b^n)(a^n + b^n) ≢ 0
  (mod n)` that yields (27)); p. 32 R1 is why the statement's *difference*
  factor is operative (Q-001);
- the author's p. 9 R2 "Quy ước" governs every denominator the main proof
  introduces (`m (h − b^n)^r ≢ 0 (mod n)`), so the cancellation at p. 32 R1 is
  the one place where a non-divisibility fact has to be *proved* rather than
  quoted.

### The work itself

The main proof has **no chunk yet**. Structure to plan against (scouted
2026-09-27, unchanged): §1.1 `H(h, b)` / `H(h, a)`, §1.2 `h = c^n`, §1.3
`h = n^{ns−1} c^n`, then the `k = 0` case and the small-`n` / `n = pk` wrap-up.
Required first pass (AGENTS.md's "Section assembly" and leaf-cap rules apply):

1. Bind the pages to signed region records and freeze the transit
   `fidelity_check.py` verdict (`PASS_WITH_MANUAL`, 19 manual pages).
2. Split into **leaf chunks** of ≤ 2 PDF pages / ≤ 10 author steps / ≤ 300 Lean
   lines each, with a `kind: section-assembly` per author section; record the
   citations of bổ đề 1–7 per leaf (that is what sets `depends_on`).
3. Screen each leaf on real instances where its hypotheses are satisfiable
   (`04-sympy/l7_common.py` shows the witness-search pattern), and record
   vacuity honestly where they are not (as L1/L2 do).
4. Then the one-step loop, unchanged: one named declaration per author step,
   compile, classify (F1–F4/S1) before the next step, stop on F4 and file a
   query — but **check the main proof's own use of a lemma first**, which is
   what turned Q-001 from F4 into F3.

At DONE (the recipe that worked for the six chunks of this session):
`#print axioms` on the assembly and every declaration (`probes/L7-ASM.axioms.lean`
is the template), fill the chunk's evidence block, `status.tsv` + YAML
`# DONE` comment, `progress.py --write PROGRESS.md`, `progress.py --check`
exit 0, `04-sympy/run_all.py`, then `compile_lean.sh <chunk>.lean` (publishes
the olean) and `compile_lean.sh Main.lean` EXIT 0 — `Main.lean` already imports
`L1`–`L7`, `L7F2`–`L7F6` and `L7ASM`.

Transcription authority: the signed REVIEWED region records
(`01-extract/regions/pNNN.yml`, all 33 pages REVIEWED, commit `9cb73f8`) plus
the 300 dpi crops; the extracted text layer is navigation only.

---

## Where the durable facts live

This file deliberately does not duplicate them:

- Environment — mounts, volumes, container policy, host resources and the
  compile cost model: `README.md`.
- Working rules — the one-step verification loop, the F1–F4/S1 outcome
  classes, and the pitfall list: `AGENTS.md`.
- Stage contracts, the `progress.py --check` evidence gate's blind spots, the
  hardening backlog, and the review → edit → re-sign runbook (a region-record
  edit flips the page to `STALE` and fails `--check` for every chunk that
  depends on it): `pipeline/PIPELINE.md`.
- Per-chunk step tables, reusable signatures and compiled patterns:
  `pipeline/03-lean/ENCODING_MAP.md` §B. Call-site ABI for every declaration of
  every DONE module: `pipeline/03-lean/SIGNATURES.md` (generated; regenerate
  after each DONE flip) — read the producer's header before writing a call.
- Live dashboard `pipeline/PROGRESS.md` (generated — never hand-edited);
  obstacle log `pipeline/BLOCKERS.md`; author queries
  `pipeline/05-feedback/`.

