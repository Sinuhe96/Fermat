# HANDOFF.md — resume point for a fresh session

Read this first, then **AGENTS.md** (binding rules, mandatory bootstrap, the
one-step verification loop, the F1–F4/S1 outcome classes) and **README.md**
(runtime commands, container policy, mount table). This file records *where
things stand* and deliberately does not repeat what those two say.

Last updated: 2026-09-26 (**ninth session**): `L6-01` (bổ đề 6) reached DONE,
so **six of the seven chunks are DONE and the only remaining verification
work is bổ đề 7** — see "Next step" below.

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
| `L7-FRAG-01` | bổ đề 7, non-divisibility conclusion | **BLOCKED** on Q-001 | parked flat copy `03-lean/Pilot/Basic.lean`; supersede with `L7/Basic.lean` |

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
`Common` and `L1`–`L6`, `Main.lean` imports them, and every producer's olean
is published, so `import Lk.Basic` resolves in a new chunk. Producer edges in
use: `L4-01 → L3-01`; `L6-01 → L3-01 + L4-01 + L5-01` (first chunk with three).

Gate status at the ninth session's close: `progress.py --check` exit 0,
`proof/check_env.sh --full` SMOKE PASS, `04-sympy/run_all.py` 7/7,
`lake build L6` exit 0.

---

## Next step — bổ đề 7 (the only remaining verification work)

### What exists

- `02-chunks/chunks/L7-FRAG-01.yml` (`pdf_pages: [1, 2, 4, 5]`) holds the
  statement, the literal `source_text`, a normalized step map **S0–S6** for
  the non-divisibility conclusion, the evidence block and the sympy screen
  (`04-sympy/test_l7_frag_01.py` exit 0: 12 witnesses at n = 7, 24 at n = 13,
  zero counterexamples to the printed statement).
- Its Lean lane was attempted **once, in a single batch** (a process
  violation: it cascaded instead of localising) and stopped at **S6 = F4**:
  `05-feedback/queries/Q-001-product-factor-sign.md` (OPEN, screenshot asset
  attached). The printed "chứng minh tương tự" line establishes ≢ 0 for the
  three pairwise **sums** `b^n+c^n`, `a^n+b^n`, `c^n+a^n`, but the first
  factor of the stated product is the **difference** `a^n − b^n`, which no
  printed step excludes. Classification F4, not F1: our transcription matches
  the print; the print is internally inconsistent (typographic).
- S0–S5 themselves reached only F2 (API shape, zero S1 yet), so the chain up
  to S5 looks codable: **restart at S0, one step per compile.** The parked
  file `03-lean/Pilot/Basic.lean` (flat copy) marks the S6 gap with one
  `sorry`; BLOCKERS **B-003** closes when this lane is redone as
  `03-lean/L7/Basic.lean` and the `import Pilot.Basic` line leaves `Main.lean`
  (`Main.lean` is not a build target — `defaultTargets` is `Testproj` — so the
  defect is latent, not active).

### Required imports for L7

The citations visible in the transcribed bổ đề 7 material are **bổ đề 5c/5d**
(Euler mod n²) and Fermat's little theorem (Mathlib). `L5_bo_de_5` exposes
exactly those, as its four conjuncts:

| print | `L5_bo_de_5 hn hodd hcop` |
|---|---|
| bổ đề 5 a) | `.1 hw` — `¬ n ∣ u+v → gcd (u+v) A = 1 ∧ ¬ n ∣ A` |
| bổ đề 5 b) | `.2.1 hw` — `n ∣ u+v → n ∣ A ∧ ¬ n² ∣ A ∧ gcd (u+v) A = n` |
| bổ đề 5 c) | `.2.2.1 hw` — `n ∣ u^n+v^n → n² ∣ u^n+v^n` |
| bổ đề 5 d) | `.2.2.2 hw` — `¬ n ∣ u → u^{n(n−1)} ≡ 1 [ZMOD n²]` (Euler, φ(n²)=n(n−1)) |

So the L7 lane's header is **`import Mathlib` + `import L5.Basic`**, it must
add `[[lean_lib]] name = "L7"` to the tracked `lakefile.toml` in the same edit
that creates `L7/Basic.lean`, and `L7-FRAG-01.yml` now carries
`depends_on: [L5-01]` (it was `[]` only because bổ đề 5 was unverified when
the fragment was frozen; the older "do the small bổ đề 5c/5đ first" directive
is satisfied by `L5-01` being DONE). S0 itself — `abc ≢ 0 (mod n) ⇒ a, b, c
≢ 0 (mod n)` — needs no author lemma at all (primality: `n ∣ a → n ∣ abc`);
the chunk's "cites bổ đề 5đ" note for it can be settled when the lane
restarts. **No L3/L4/L6 declaration is cited by the transcribed material**;
confirm the citations of the remaining proofs (below) when they are
transcribed — that is when their `depends_on` gets set.

### Still to chunk inside bổ đề 7

Four conclusion groups are already in `L7-FRAG-01.yml`'s `source_text` but not
chunked (their proofs are on pp. 2/4/5; displays (a) and (d) are in the
transcribed p. 4 → p. 5 proof):

1. `a^{n²} + b^{n²} − c^{n²} ≡ 0 (mod n²)` (display (a), from bổ đề 5d);
2. `a^{n(n−3)} + b^{n(n−3)} + c^{n(n−3)} ≡ c^{3n} + b^{3n} ≡ a^{3n} − b^{3n}
   ≡ b^n c^n + a^{2n} ≡ c^n a^n + b^{2n} ≡ b^n a^n − c^{2n} ≡ 0 (mod n²)`;
3. `n ≡ 1 (mod 6)`;
4. `a^{n(n−2)} + b^{n(n−2)} − c^{n(n−2)} ≡ a^{n(n−4)} + c^{n(n−4)}
   ≡ b^{n(n−4)} + c^{n(n−4)} ≡ a^{n(n−4)} − b^{n(n−4)} ≡ 0 (mod n²)`.

Same single producer edge (`L5-01`), same one-step loop. Screen these **on
real instances**, not by vacuity — bổ đề 7's hypotheses are satisfiable (the
fragment's screen found witnesses), unlike `L1-01`/`L2-01`, whose screens are
inference-based because their FLT hypotheses have no witnesses for n ≥ 3.

### Closing recipe

Follow AGENTS.md's one-step loop and outcome classes exactly: freeze the step
map → screen → one named declaration per author step → compile → classify
before the next step → stop on F4 and file a query. At DONE: `#print axioms`;
fill the chunk's evidence block (`regions`, `renders`, `lean_decls`); update
`status.tsv` + the YAML; `progress.py --write PROGRESS.md`; `progress.py
--check` exit 0; `04-sympy/run_all.py`; then `lake build L7` (publishes the
olean) and `lake env lean Main.lean` exit 0 with the `Pilot` line replaced —
that last command is the sorry-free "everything typechecks" gate B-003 asks
for. Q-001 stays with the author: **no L7 completion without their sign
answer.**

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
- Live dashboard `pipeline/PROGRESS.md` (generated — never hand-edited);
  obstacle log `pipeline/BLOCKERS.md`; author queries
  `pipeline/05-feedback/`.

