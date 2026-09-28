# HANDOFF.md — resume point for a fresh session

Read this first, then **AGENTS.md** (binding rules, mandatory bootstrap, the
one-step verification loop, the F1–F4/S1 outcome classes) and **README.md**
(runtime commands, container policy, mount table). This file records *where
things stand* and deliberately does not repeat what those two say.

Last updated: 2026-09-28 (**thirteenth session**): **the main proof (pp. 6–33) is
open and moving, and the ledger is 16/16 DONE.** This session closed `B-01`
(section B, p. 2 — the two sum-transformation rules the main proof cites 11 times
from p. 9 on), so all three recorded chunks of the main-proof lane are DONE:
`M1-FRAG-01` (p. 6 `P006-R1`: the bổ đề 6 substitution + sign symmetry),
`M1-FRAG-02` (the printed (7) and (7′)), `B-01` (B.1/B.2). `M1-FRAG-03` (the
printed (8), (9), (10)) is written and **in flight** — its Lean file exists and
is being compiled, it has **no chunk record yet**, and it enters the ledger only
when it is green (see the lane-state section below for its exact state).

Two changes to the *method*, not just the state:

- **A circularity instrument now exists**: `01-extract/cite_index.py` indexes
  every printed label against every citation site in document order and reports
  forward / reused / repeated / dangling labels (0.5 s, host-side, exit 0). Over
  pp. 1–33: **zero forward or cyclic citations** — every citation points backward
  — but two printed results are cited and **never printed**: `(16)` and `(26)`,
  both on p. 32, the step that closes the `h = c^n` case split; the missing `(26)`
  slot is exactly where the one inference the print does not supply lives
  (`H(c^n,b) ≡ H(c^n,a)` gives equality, and the step asserts both are `≡ 0`).
  Filed as `05-feedback/queries/Q-003` (**OPEN**). Label collisions plus four
  same-class printed factor misprints are `05-feedback/queries/Q-004` (**OPEN**).
  **Read both before writing any leaf from p. 14 or pp. 31–32.**
- **The compile cost model was wrong for failing rounds and is now measured**: a
  round that *fails* costs **7–24 s**, not 250–400 s — Mathlib's oleans are
  cached in the work volume, so the multi-minute rounds are the ones where heavy
  `ring`/`omega` work elaborates *successfully*. Recorded in
  `03-lean/MATHLIB_API_LESSONS.md` items 5–8, with two traps that each cost a
  round here: `omega` cannot prove truncated-subtraction monotonicity
  (`y ≥ m - k ⊢ m - 1 - y < k` — it abstracts `↑(m-k)` as an atom), and
  `Finset.sum_subset` puts the **smaller** set's sum on the left (it is a
  `to_additive` image of `prod_subset`, so `rg` cannot find the declaration
  either).

Environment note: the `lean` container was **rebuilt** (10 GB RAM cap, new
`proof/mem_watch.sh`) and re-verified — `check_env.sh --full` →
`SMOKE PASS (full)`: Lean 4.35.0-rc2, mounts/Lake project/Mathlib cache OK,
`import Mathlib` OK. Volumes survived. The lane watchdog runs as service
`watch-m1` (`proof/watch_lane.sh` → `03-lean/M1_watch.log`, 60 s heartbeat,
`latched=none`); its informational `lastlog` metric was fixed this session (it
globbed only `*compile*.log`, so this lane's `*_round*.log` files were invisible
to it — the latch logic never read that value, but a stale metric is worse than
none).

---

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
| `B-01` | section B, p. 2: B.1 index shift + B.2 falling-factorial sum = `f^{(k)}(x)` | DONE | `03-lean/B/Basic.lean` (namespace `B`), `lean_lib B`, logs `03-lean/B-01-s2deriv_round{17,18,20}.log` + `B-01-axioms_round21.log` |
| `M1-FRAG-01` | main proof §1, p. 6 `P006-R1`: the bổ đề 6 substitution + sign symmetry | DONE | `03-lean/M1F1/Basic.lean`, `lean_lib M1F1`, log `03-lean/M1-FRAG-01-S0-S1-S3-S4-axioms_round4.log` |
| `M1-FRAG-02` | main proof §1, p. 6 `P006-R2`: the printed (7) and (7′) | DONE | `03-lean/M1F2/Basic.lean`, `lean_lib M1F2`, logs `03-lean/M1-FRAG-02-support_round1{0..3}.log` + `M1-FRAG-02-S0-S1-axioms_round1{4,5,6}.log` |
| `M1-FRAG-03` | main proof §1, p. 6 `P006-R2`: the printed (8), (9), (10) | **in flight** | `03-lean/M1F3/Basic.lean`, `lean_lib M1F3` — file written, no chunk record yet |

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

### Lane opened 2026-09-28 — live state in `pipeline/03-lean/M1_LANE.md`

**Read `M1_LANE.md` first.** It holds the lane's round protocol, the mechanical
watchdog (`proof/watch_lane.sh` → `M1_watch.log`), the round harness
(`proof/run_round.sh`), the circuit breakers, the observer protocol, the
consolidated chunk plan (§5) and the findings log (§7–§8).

**The main proof is no longer unchunked: `M1-FRAG-01` (p. 6, `P006-R1`) is
DONE.** Four declarations, all S1 — round 4 returned EXIT 0, 341 s, zero
errors, zero warnings, zero `sorry`, with `#print axioms` showing only
`[propext, Classical.choice, Quot.sound]`: the bổ đề 1 reduction
(`M1F1_step_S0_reduce`), the four-form `u/v/t` sign symmetry via `Odd.neg_pow`
(`M1F1_step_S1_symmetry`), the bổ đề 6 substitution (`M1F1_step_S3_bo_de_6`,
where `n ∤ u*v` is derived from S2's two non-divisibilities through
`Int.prime_iff_natAbs_prime` + `Prime.dvd_mul`), and the substitution into (3)
(`M1F1_step_S4_substitute`). The author's WLOG `n ∤ u`, `n ∤ v` (S2) is **not** a
declaration: the print assumes it, so it is carried as S3's two hypotheses.
`M1-FRAG-02` (the printed (7) and (7′)) is recorded with its two steps, and the
support lemmas they need are written. `B-01` is the only chunk `progress.py`
lists as ready-to-start.

**B.1 is encoded in the range form both sides share**
(`Σ_{i<N} a (k+i) = Σ_{i<N} a (m+i-m+k)`), not the literal `Icc` form: the
latter needs the range equality `(n+1)-k = (n+m-k+1)-m`, which is *true* in ℕ
but which `omega` rejects with a spurious counterexample, because truncated
subtraction is not linear. Anyone re-attempting the `Icc` form should budget for
a hand-rolled case split whose content is ℕ bookkeeping, not the author's rule.

What the earlier window established:

- **Section B is a missing prerequisite.** `B. MỘT CÁCH BIỂN ĐỔI TỔNG Σ₃ …`
  sits in `P002-R1`, and the main proof cites `mục B.1` / `mục B.2, trang 2`
  at **11 sites from p. 9 on**. No DONE chunk covers it (`L1-01`…`L7-ASM`
  verify section C, the lemma proofs, on the same page and after). Chunk
  **`B-01`** is now recorded as TODO — `source_text` byte-copied from the signed
  region record, independent crop read done, sympy screen green — and it is a
  prerequisite of leaves 11, 15, 16, 18, 19, 20. The ledger is now 16 rows
  (13 pre-existing DONE + `M1-FRAG-01` DONE + `B-01` and `M1-FRAG-02` TODO).
- **Chunk plan consolidated:** 41 leaves in source order, ids final
  (`M1-FRAG-01` … `M1-FRAG-41`), plus `M1-ASM-A`…`E` per printed section and
  `M1-THM`. The final assembly home is `P033-R2`. Packing rule: one compile
  round costs 250–400 s regardless of leaf size, so leaves are packed toward
  ~8–10 steps; scale ≈ 250–400 rounds ≈ 20–35 h.
- **Numeric screens green** (`docker compose exec -T lean python
  /workspace/pipeline/04-sympy/m1_common.py`, EXIT 0): the §1.1 expansion core;
  the *unconditional* tail truncations behind (7)/(7′)/(8)/(9)/(10) with sharp
  moduli; the p. 6 triple-sum `l+j` regrouping (all ten printed index ranges are
  the natural `[l, n−1−j]`); p. 7 R1's RHS; section B's two rules (B.2's
  derivative form confirmed symbolically). The screens also fix a statement
  constraint: **(7)–(10) are conditional on the equation `u^n+v^n=t^n`**, only
  their tail divisibility is unconditional.
- **Crop-verify before encoding anywhere in pp. 12–28.** Colour carries the
  algebra there and the signed LaTeX does not record it. Nine regions are
  flagged; four crops are read already (`P023-R2`, `P025-R1`, `P026-R2`,
  `P016-R2`), five remain. The reads so far **confirm the signed transcription**
  and therefore expose *printed* inconsistencies — candidate F4s, not our
  transcription errors: `P023-R2` twice (a `7` that only covers three of four
  summands; `6b^{n(n−2)}` without its `n`), `P025-R1`/`P026-R2`
  (`2n(n−1)` vs `2(n−1)`, difference `n^{4s}` — not absorbable mod `n^{4s+2}`),
  `P016-R2` vs `R3`/`P017-R1` (exponent turnover `n(n−3)`→`n(n−2)` with the
  `(a^n+2n^s abck)` factor). Also: labels **(16)** and **(26)** are cited but
  defined nowhere in pp. 1–33, and `P033-R1` prints `55/3` where its own
  coefficients sum to `55/4`.
- **The deep risk is the (27) cancellation at `P032-R1`** (§1.2, on the critical
  path): it is the one step that must be *proved*, and the printed "vì" clause
  is an assertion whose factor list differs from bổ đề 7's product, with
  `¬n ∣ a^n + b^n` never printed.
- **Two rules the next session must keep:** one compile at a time (the work
  modulus `n^{4s+2}` is composite, so `ZMod (n^{4s+2})` has no `Field` instance
  and `field_simp` is unavailable — formalize denominator-cleared, and classify
  each printed line `=` vs `≡ (mod n^{4s+2})` individually), and crop-read first
  in pp. 12–28. §2's Dirichlet/Lamé/Kummer lines for `n = 5, 7, 11` must become
  explicit **hypotheses** of `M1-ASM-E`, never axioms.
- **Tooling:** `progress.py --write` needs the **absolute** path
  (`/workspace/pipeline/PROGRESS.md`) — the container's cwd is
  `/workspace/work`; long `docker compose exec` runs get backgrounded by the
  harness; region `latex` lines exceed 768 chars and need `sed`/`fold`; do not
  hand-type Vietnamese literals into scripts (they do not match the file's
  bytes) — anchor extraction on ASCII fragments.

### Lane state at the thirteenth session (2026-09-28) — `M1-FRAG-03` DONE (17/17), `M1-FRAG-04` in flight (S0+S1+S2-first-half of 8)

- **Current edge (round 37)**: `M1-FRAG-04` — pp. 6–7, the `l+j` regrouping that
  follows the printed (8)–(10) — is IN PROGRESS with **S0, S1 and the first half
  of S2 written and certified**: the triple-sum expansion (`M1F4_step_S0_triple`)
  and the printed right-hand side (`M1F4_step_S1_binomial`), on the support
  lemmas `M1F4_add_pow_neg`, `M1F4_absorb`, and now `M1F4_sum_complement` (the
  pointwise filter complement behind the `l+j ≥ 5` split, proved generically in
  the summand). Round 37 certificated all three: EXIT 0, 0 warnings, permitted
  axioms only (`propext`/`Classical.choice`/`Quot.sound`), no `sorryAx`.
- **S2's content is frozen and verified** (2026-09-28): the printed boundary
  display is **one sum for each pair `(j,l)` with `j + l ≤ 4` — fifteen of them**
  (`C(6,2) = 15`), not the ten an earlier note guessed, and **each printed range
  is exactly the natural `i ∈ [l, n-1-j]`** with the triple sum's own summand. So
  that display carries **no misprint** — a positive result that also confirms the
  sympy screen's "partition exact" at representation level. The remaining work of
  S2 is the **re-indexing half** (the two index sets are the same set in a
  different order); its statement, the bijection proof obligations, and the
  recommended `Finset.sigma` + `Finset.ext` + `omega` route are written into
  `M1-FRAG-04.yml`. Estimated 40–80 lines, several rounds — the leaf's most
  expensive step. Then S3–S7 (the fifteen boundary sums in their printed
  factorial forms and the `i ≥ 5` rewrite via `M1F4_absorb`).
- **The lane's first F1 was caught here** (round 31, 9 s) and it is the single
  most valuable thing to read before touching p. 6 R3: the printed alternate form
  `Σ_i C(n,i) a^{n(n-1-i)} (n^s abck)^i` is **ℕ-unsafe at `i = n`** — `n - 1 - i`
  truncates to `0`, losing a factor `a^n`, so the natural split identity is simply
  false there. The two printed forms are equal only as ℤ-exponent expressions
  (measured: difference 0 at n = 5, 7). Encode the `p. 6 R2` form. See the
  corrected §7 note and `MATHLIB_API_LESSONS.md` item 11.

Read `pipeline/03-lean/M1_LANE.md` §1 (round protocol), §3 (breakers), §7
(findings, including the circularity audit) and §8 (the per-round table) for the
live detail. Summary of the current edge of the lane:

- **Done and recorded**: `M1-FRAG-01`, `M1-FRAG-02`, `B-01` (all three S1 with
  permitted axioms only). `B-01` needed rounds 17/18/20 (two F2 arithmetic/
  direction errors, one probe round) and round 21 for its axioms gate; `B.2`'s
  second equality is `M1F3`'s shape in miniature: `Polynomial.iterate_derivative_*`
  with the falling-factorial sum over `range (m-k)` (see `B-01.yml` for the
  resolved name check and `ENCODING_MAP` for the pattern).
- **Done (round 28)**: `M1-FRAG-03` = the printed (8) mod `n^{3s+1}`, (9) mod
  `n^{4s+1}`, (10) mod `n^{5s+1}` — one leaf, three steps, since they are the
  same expansion at orders 2, 3, 4. Lean file `03-lean/M1F3/Basic.lean`
  (`lean_lib M1F3` added, `gen_signatures.py` `MODULES` updated). Its own support
  is five declarations: an `X`-indexed binomial expansion `M1F3_add_pow_index`, a
  two-case tail divisibility `M1F3_tail_dvd`, an `r`-parameter truncation
  `M1F3_expand_trunc` (of which `M1F2_expand_trunc` is the case `r = 1`), and the
  three steps `M1F3_step_S0_eight`, `M1F3_step_S1_nine`, `M1F3_step_S2_ten`.
  It is deliberately **self-contained** (no `import M1F2.Basic`): the higher
  printed moduli need `n^((r+1)s+1) ∣ C(n,j)X^j` for `j ≥ r+1`, which
  `M1F2_choose_mul_pow_dvd` cannot supply because it only extracts `n^(2s+1)`.
  Four rounds so far, all F2, each a distinct mechanical defect — `omega` on a
  non-linear product (`(r+1)*s` vs `2*s`), a `rw ... at` target list that
  demanded each lemma match *every* hypothesis, an unavailable divisibility
  route, and `dvd_mul_of_dvd_right` vs `_left` (the former yields `c * b`). No
  mathematical obstruction has appeared; rounds 22→24 went 8→2→4 error lines
  with each fix a real defect. **If the next round shows anything mathematical,
  stop and record the file as unfinished rather than pushing further** — this is
  the lane's own breaker rule (3 consecutive failures on one step ⇒ bounded
  search / observer), exceeded here only because every failure was mechanical.
- **Next after that**: `M1-FRAG-04`+ (p. 6 R3's triple sum, then pp. 7–8), then
  `M1-ASM-A…E` and `M1-THM`. The assemblies are the last place a circularity
  could hide (a leaf may take the author's equation as a hypothesis; any
  hypothesis no chunk discharges is the thing to look for).

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

Gate status at the thirteenth session (2026-09-28), all re-run after the
container rebuild: `check_env.sh --full` → **SMOKE PASS (full)** (Lean 4.35.0-rc2,
Lake project + Mathlib cache OK, `import Mathlib` OK); `progress.py --check`
exit 0 with **17/17 DONE**, 0 obstacles, **2 OPEN author queries** (Q-003,
Q-004); watchdog `watch-m1` live with `latched=none` and no `M1_inflight`
outstanding. Round ledger: `03-lean/M1_rounds.tsv` — 38 rounds so far,
classified **14 S1 / 20 F2 / 2 ENV / 1 F1 / 1 PROBE** (the F1 is the p. 6 R3
`ℕ`-unsafe exponent form). The measured cost model matters for planning: a
*failing* round costs 7–24 s (Mathlib oleans are cached), so iterate freely on
compile errors; only successful rounds with heavy `ring`/`omega` take minutes.

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

