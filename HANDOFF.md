# HANDOFF.md — resume point for a fresh session

Read this first, then **AGENTS.md** (binding rules, mandatory bootstrap, the
one-step verification loop, the F1–F4/S1 outcome classes) and **README.md**
(runtime commands, container policy, mount table). This file records *where
things stand* and deliberately does not repeat what those two say.

Last updated: 2026-09-26 (**tenth session**): the `L7-FRAG-01` Lean lane was
restarted one-step-per-compile, and its non-divisibility chain now verifies
**S0–S5, all S1**, in `03-lean/L7/Basic.lean` (sorry-free, permitted axioms
only). Only **S6** — the printed product — is left, and it is F4, blocked on
author query Q-001. So six chunks are DONE and one is BLOCKED; BLOCKERS B-003
is resolved. See "Next step" below.

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
| `L7-FRAG-01` | bổ đề 7, non-divisibility conclusion | **BLOCKED** on Q-001 (S0–S5 = S1; S6 = F4) | `03-lean/L7/Basic.lean`, `lean_lib L7`, log `03-lean/L7-FRAG-01_compile_20260926.log`; pre-restart exhibit `03-lean/Pilot/Basic.lean` (frozen, imported by nothing) |

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

Gate status at the tenth session's close (2026-09-26): `progress.py --check`
exit 0, `proof/check_env.sh` SMOKE PASS, `04-sympy/run_all.py` 7/7,
`compile_lean.sh L7/Basic.lean` EXIT 0 (zero warnings, zero `sorry`; `#print
axioms` on all nine declarations = propext / Classical.choice / Quot.sound
only), and `compile_lean.sh Main.lean` EXIT 0 — the aggregate root now compiles
every chunk including L7, which is the "everything typechecks" gate B-003
asked for (B-003 RESOLVED).

---

## Next step — bổ đề 7 (the only remaining verification work)

### What exists

- `02-chunks/chunks/L7-FRAG-01.yml` (`pdf_pages: [1, 2, 4, 5]`) holds the
  statement, the literal `source_text`, a normalized step map **S0–S6** for
  the non-divisibility conclusion, the evidence block and the sympy screen
  (`04-sympy/test_l7_frag_01.py` exit 0: 12 witnesses at n = 7, 24 at n = 13,
  zero counterexamples to the printed statement).
- Its Lean lane was attempted **once, in a single batch** on 2026-09-25 (a
  process violation: it cascaded instead of localising) and is now
  **superseded**. The 2026-09-26 restart redid it one step per compile:
  `03-lean/L7/Basic.lean` verifies **S0–S5, all S1** (nine declarations,
  EXIT 0, zero warnings, zero `sorry`, axioms = propext / Classical.choice /
  Quot.sound). S0–S2 are `ZMod n` statements; S3–S5 are carried out in ℤ
  congruence/divisibility form (`L7_pair_reductio` is the printed reductio with
  the pair abstracted — the print's own "chứng minh tương tự" — and
  `L7_tail_three` is its printed tail, Fermat/3 ≡ 0/n = 3). S5a is an F3
  fill-in from the author's own (b) plus S0. Per-round diagnosis:
  `03-lean/L7-FRAG-01_compile_20260926.log`; the ZMod-vs-ℤ lesson that forced
  the rewrite is the L7 session entry in `MATHLIB_API_LESSONS.md` (and §B Chunk
  L7-FRAG-01 in `ENCODING_MAP.md`).
- **S6 remains F4**:
  `05-feedback/queries/Q-001-product-factor-sign.md` (OPEN, screenshot asset
  attached, no declaration encodes it). The printed chain establishes ≢ 0 for
  the three pairwise **sums** `a^n+b^n` (S5a), `b^n+c^n` (S3+S4), `c^n+a^n`
  (S5b), but the stated product's first factor is the **difference**
  `a^n − b^n`, which no printed step excludes. Classification F4, not F1: our
  transcription matches the print; the print is internally inconsistent
  (typographic). The pre-restart file `03-lean/Pilot/Basic.lean` is kept as a
  frozen exhibit for that query (its single `sorry` marks the gap) and is
  imported by nothing; BLOCKERS **B-003** is RESOLVED (the `import Pilot.Basic`
  line left `Main.lean`, and `compile_lean.sh Main.lean` now exits 0).

### Wiring (in place since the tenth session)

The lane's header is **`import Mathlib` + `import L5.Basic`**; `lakefile.toml`
declares `[[lean_lib]] name = "L7"` with `roots = ["L7.Basic"]`, and
`Main.lean` lists `L7.Basic` in the verified set (the `Pilot` line and the
`Pilot` `lean_lib` entry are gone). `L7-FRAG-01.yml` carries
`depends_on: [L5-01]`. Fermat's little theorem in the tail is bổ đề 5's
`L5_gcd_eq_one_of_not_dvd`; `L5_bo_de_5`'s conjuncts `.2.2.1` (5c) / `.2.2.2`
(5d) are what bổ đề 7's **other** conclusions need when their chunks arrive.

### The bổ đề 5 surface this chunk reuses

`L5_bo_de_5`'s four conjuncts (the print's parts a)–d)), at
`L5_bo_de_5 hn hodd hcop`:

| print | `L5_bo_de_5 hn hodd hcop` |
|---|---|
| bổ đề 5 a) | `.1 hw` — `¬ n ∣ u+v → gcd (u+v) A = 1 ∧ ¬ n ∣ A` |
| bổ đề 5 b) | `.2.1 hw` — `n ∣ u+v → n ∣ A ∧ ¬ n² ∣ A ∧ gcd (u+v) A = n` |
| bổ đề 5 c) | `.2.2.1 hw` — `n ∣ u^n+v^n → n² ∣ u^n+v^n` |
| bổ đề 5 d) | `.2.2.2 hw` — `¬ n ∣ u → u^{n(n−1)} ≡ 1 [ZMOD n²]` (Euler, φ(n²)=n(n−1)) |

Citations are settled for this fragment: S0 needs no author lemma and no
primality (`n ∣ a → n ∣ abc`, now encoded and verified), S1/S2 restate GT2/GT3,
and the S3–S5 chain cites only Fermat's little theorem (via bổ đề 5's helper).
**No L3/L4/L6 declaration is cited by the transcribed material**; the four
remaining conclusion groups below rest on bổ đề 5c/5đ — confirm their citations
when they are transcribed, which is when their `depends_on` gets set.

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

The non-divisibility fragment's own loop is finished: S0–S5 are S1 and its
wiring, evidence and logs are in place. What is left is:

1. **S6 / Q-001** — nothing to do until the author answers whether the
   product's first factor is the difference `a^n − b^n` (the printed proof's
   coverage gap) or whether the "chứng minh tương tự" line should read
   `a^n − b^n` (making the product's factor a sum). Once answered, either
   encode the corrected S6 (a `DONE` flip needs the chunk's evidence block
   refreshed and `progress.py --check` green) or, if the answer changes the
   printed text, re-review the affected region records (`regions.py signoff`)
   before re-transcribing — a region edit flips the page to `STALE` and fails
   `--check` for every dependent chunk.
2. **The four conclusion groups still unchunked** (below): one chunk each,
   same one-step loop, same single producer edge `L5-01`, with `depends_on`
   set when their citations are confirmed.

Use AGENTS.md's loop and outcome classes unchanged: freeze the step map →
screen → one named declaration per author step → compile → classify before the
next step → stop on F4 and file a query. At DONE: `#print axioms`; fill the
chunk's evidence block (`regions`, `renders`, `lean_decls`); update
`status.tsv` + the YAML; `progress.py --write PROGRESS.md`; `progress.py
--check` exit 0; `04-sympy/run_all.py`; then `compile_lean.sh <chunk>.lean`
(publishes the olean) and `compile_lean.sh Main.lean` EXIT 0 (the aggregate
gate B-003 asked for, now in place).

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

