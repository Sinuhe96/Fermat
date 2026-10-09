# HANDOFF_CONJECTURE.md — side-lane: n-adic valuation conjecture (Phase 4)

**This lane is NOT the PDF FLT verification.** Do not touch `HANDOFF.md`,
`status.tsv`, chunk YAMLs, `PROGRESS.md`, or any `L*`/`M1*` pipeline file
from this lane. Shared infra (`docker compose`, `lake-work` volume,
container) is used read-only/quietly: never run two `lake env lean`
processes at once, never `docker compose down -v`, never rebuild images.

## The conjecture (author-confirmed reading 2)

Let `n = 6l + 1` be prime, with `n, a, b, a+b, a²+ab+b²` pairwise coprime.
Let `P(a,b) = (a+b)^n - a^n - b^n`. Claim under study: `v_n(P) ≥ 3` has
NO solutions in positive `l, a, b` (i.e. `v_n(P) ≤ 2` always).

Equivalent finite form (the screen's basis): with
`f(x) = ((x+1)^n - x^n - 1)/n` and `x = a·b⁻¹ mod n²`,
`v_n(P) ≥ 3 ⟺ n² ∣ f(x₀)` at a valid root `x₀` of `f mod n`.

## Evidence already established (Python/C screens, 2026-09-30)

- Zero counterexamples: primes < 2.6×10⁶ (uint64 `n³` ceiling),
  92,854 valid roots, `roots.csv` in container `/workspace/work/`.
- Cube channel (`a=b=1`, `n³ | 2ⁿ-2`): no hits < 2⁶⁴ — this slice is
  open in the literature (beyond Wieferich, p≡1 mod 6), so the full
  conjecture is NOT expected to fall in this session.
- Structural theorems derived (paper-side, to be formalized here):
  factorization identity; non-liftable roots (`F'(x₀) ≡ 0 mod n²`);
  fiber-constancy (one representative per root is exhaustive).
- `screen_conjecture.c` (repo root) + `Phase2_Feedback.md` (Gemini's
  review; its Phase-4 block plan accepted with Block 4 redesigned —
  see below).

## Phase-4 block plan (accepted 2026-09-30)

1. **Block 1 — factorization identity over `ℤ[X]`** (current):
   `(X+1)^n - X^n - 1 = C n * X * (X+1) * (X²+X+1)² * E`,
   `E` monic, for prime `n = 6l+1`, `l ≥ 1`.
   Proof route decided (see CJ/PROBE.lean for pinned names):
   - `n`-part: `Polynomial.C_dvd_iff_dvd_coeff` + `Nat.dvd_choose_add`
     (coeffs of F are `n.choose k` for `0<k<n`, else 0);
   - `X` and `X+1` parts: `Polynomial.dvd_iff_isRoot` (eval 0 and
     −1; `Odd.neg_pow` for `(−1)^n = −1`);
   - `(X²+X+1)²` part — the double root, hardest piece:
     * step A `D ∣ F`: quotient induction in
       `ℤ[X] ⧸ Ideal.span {X²+X+1}` (`modByMonic_eq_zero_iff_quotient_eq_zero`):
       in the quotient `mk X³ = 1`, `mk (X+1)³ = −1`, so
       `mk F(l+1) = mk F(l)` with `mk F(0) = 0`;
     * step B `D ∣ F' = C n ((X+1)^{6l} − X^{6l})`: same quotient,
       both 6l-th powers are 1 → `mk F' = 0`, hence with
       `G := F /ₘ D` and `derivative_mul`: `(2X+1)·G = D·K` in `ℤ[X]`;
     * cancellation: `ℚ[X]` route — `X²+X+1` irreducible
       (`irreducible_of_degree_le_three_of_not_isRoot` + `(2x+1)² = −3`),
       `Irreducible.prime` → `Prime.dvd_or_dvd` → `D ∤ (2X+1)` (degree)
       → `D ∣ G` over `ℚ` → monic-division bridge back to `ℤ`
       (`modByMonic_add_div` + degree contradiction), so `D² ∣ F`;
   - combine coprime factors with `IsCoprime.mul_dvd`
     (`X`, `X+1`, `X²+X+1` pairwise coprime — Bezout: `−X + (X+1) = 1`,
     `D(0)=1`, `D(−1)=1`);
   - assemble the identity from the component divisibilities.
2. **Block 2 — valuation decomposition**: `v_n(P) = 1 + v_n(E)` under
   the pairwise-coprime hypotheses (`padicValNat_dvd_iff_le`,
   `padicValNat.mul`). Needs Block 1 + homogenization to `E₂(a,b)`
   (bivariate: `P(a,b) = n·a·b·(a+b)·(a²+ab+b²)²·E₂(a,b)`).
3. **Block 3 — non-liftable roots + fiber-constancy** (the gem):
   `F'(x) = n²(q(x+1) − q(x))` exact integer identity; Taylor step
   `E(x₀+nt) = E(x₀) + nt·E'(x₀) + n²t²·G` (integral division).
4. **Block 4 — verifier exhaustiveness (REDESIGNED, not Gemini's
   literal statement)**: prove in-kernel
   `verifier B = ok → ∀ n < B, v_n P < 3`; keep the big run external
   (recorded output, not kernel-checked). Small-bound anchor
   `n < 10³–10⁴` via `native_decide` if cheap. The `n < 2.6×10⁶`
   theorem as a kernel-checked Lean statement is INFEASIBLE
   (~1.2×10¹¹ powmods, single-threaded) — never `sorry` it.

## Round protocol (this lane)

- Source of truth: `pipeline/03-lean/CJ/` (PROBE.lean, Basic.lean …).
- One round: write `pipeline/03-lean/CJ_inflight` = `"R<n>\t<epoch>\t<file>"`,
  run
  `docker compose exec -T lean sh -c 'sh /workspace/proof/compile_lean.sh CJ/<file>.lean > /workspace/pipeline/03-lean/CJ_<tag>.log 2>&1; echo "EXIT=$?" >> …'`
  as a tracked background job (never foreground — the 10-min cap kills
  `lake`), then delete `CJ_inflight` when the job reports.
- Read `CJ_watch.log` LATCH lines before every round (watchdog
  `LANE=CJ proof/watch_lane.sh`, service `watch-cj`).
- Batch every `#check` into ONE file (import Mathlib floor ≈150–350 s/round).
- Ladder: local grep on `proof_verify/.lake/packages/mathlib/Mathlib/`
  first (free), Loogle JSON via curl, in-file tactics last. NEVER
  `#loogle`/`#leansearch` in this container (they hang).
- `#print axioms` on every final theorem: only `Classical.choice`,
  `propext`, `quot.sound`. `sorry` allowed ONLY as in-progress
  scaffolding; the lane's final report must state honestly which
  blocks are S1 and which are open.

## Status log

- 2026-09-30: session start. Skills loaded (fermat-lean-mathlib
  harness skill + repo SKILL.md/search.md/reference.md; lean4 canonical;
  lean-proof canonical; MATHLIB_API_LESSONS §1–300; ENCODING_MAP §A–B;
  later per-chunk sections of those two ledgers were skipped as
  PDF-lane-specific). Container green, testproj initialized, M1 dormant
  (last activity 2026-09-28, no in-flight). Probe round 1 launched
  (`CJ/PROBE.lean` → `CJ_probe.log`).
- **SESSION RESULT — Block 1 COMPILES, EXIT=0** (round 8, `CJ_r8.log`).
  `#print axioms`: `D_dvd_F`, `X_dvd_F`, `X1_dvd_F`, `n_dvd_F` all
  **sorry-free** (only `propext, Classical.choice, Quot.sound`).
  `D2_dvd_F` and `CJ_block1` carry `sorryAx` from exactly ONE intended
  `sorry`: **`D_dvd_of_deriv_rel`** (the ℚ[X] cancellation bridge,
  line ~184), whose full proof route is spelled out in its docstring
  (irreducible → `Prime.dvd_or_dvd` → natDegree exclusion → monic
  division descent via `natDegree_modByMonic_lt`).
- Rounds R1–R8 (`CJ_r1.log` … `CJ_r8.log`); R8 = EXIT=0. Round
  protocol worked: `CJ_inflight` handshake → container-side log →
  `watch-cj` latched nothing (0 latches all session).
- API pitfalls this session cost 7 fix-rounds — ALL appended to
  `pipeline/03-lean/MATHLIB_API_LESSONS.md` §"Side-lane CJ" (one_mul,
  coeff_sub-before-coeff-lemmas, `abbrev` for quotient aliases,
  simp-normalizes-C1, if-lemma deprecations, pow_add pinning, rw
  directions).
- Cosmetic leftovers (non-blocking): deprecation warnings for
  `if_true/if_false` (working; rename to `ite_true/ite_false` when
  touching those lines), unused simp args in n_dvd_F lists, unused
  unprimed `mkQ_Y6/mkQ_X6` in the quotient_deriv list.
- **R11–R17 (current session): Blocks 2, 3a, and Block 1 all GREEN,
  EXIT=0.** R13 (`CJ_r13.log`): `CJ_valuation` (univariate valuation
  decomposition `v_n(F x) = 1 + v_n(E x)`), `CJ_deriv`, `CJ_nonlift`
  axiom-clean = S1. R14–R17 (`CJ_r17.log`): `D_dvd_of_deriv_rel` proved
  (map to ℚ[X] via `Int.castRingHom ℚ`; `X²+X+1` irreducible via
  `irreducible_of_degree_le_three_of_not_isRoot` + `(2x+1)² = -3`
  nlinarith; `Irreducible.prime` + `Prime.dvd_or_dvd`, branch
  `D ∣ φ(2X+1)` excluded by natDegree arithmetic; descent via
  `modByMonic_add_div` + degree bound) — the file's LAST `sorry` gone;
  `CJ_block1`/`D2_dvd_F` axiom-clean. API lessons 28–33 recorded
  (Fact.out instance-implicit receiver; padicValNat.pow rw-pattern;
  abbrev-blind rw; protected `Polynomial.map_*`; no `IsSimpleRing ℤ`;
  `natDegree_modByMonic_lt` arg order). Next: Block-2 homogenization
  `E₂(a,b)`, then Block 3b (fiber-constancy), then Block 4.
- **R18–R30 EXIT=0 — Block 2 COMPLETE, homogenization included**
  (`CJ_r30.log`). Probe file cleaned (pinned-absent names commented,
  expected-fail repros removed → `CJ_probe.log` EXIT=0). New theorems:
  `homog_ident` (distributes `Polynomial.homogenize` over Block 1 at
  total degree `n`, splits 1+1+4+(n−6)), `CJ_homog` (∃ E₂,
  `P(a,b) = n·a·(a+b)·(a²+ab+b²)²·E₂(a,b)`; `b ≠ 0` guards the ℚ eval
  bridge; `E₂ a b = (homogenize E (n-6)).eval ![a,b]`),
  `CJ_valuation_P` (`v_n(P) = 1 + v_n(E₂)` from the factorization +
  reading-2 coprimality) — all axiom-clean = S1. **File has zero
  `sorry`.** E₂ carries one extra factor `b` vs Gemini's
  `n·a·b·(a+b)·…·Eₙ` packaging (valuations agree under `n ∤ b`).
  API lessons 34–39 recorded. Next: Block 3b (fiber-constancy), then
  Block 4 (verifier).
- **R35–R38 EXIT=0 — Block 4a `CJ_witness_iff` S1 + verifier core
  surfaced** (`CJ_r38.log`). `CJ_witness_iff` (`v_n(P) ≥ 3 ↔ n² ∣ E₂v`
  from `CJ_valuation_P` + `padicValNat_dvd_iff_le`) and `fInt`/`fInt_eq`
  (`F/n` as exact `ℤ` division via `eval_dvd` + `Int.ediv_mul_cancel`)
  all axiom-clean. **File: zero `sorry` across Blocks 1/2/3 + 4a.**
  API lessons 44–45 recorded (Block 4a `.mp`/`.mpr` direction; `fInt`
  `ℕ→ℤ` cast; `eval_dvd` implicit-`x`; `ediv_mul_cancel'` absent).
- Block status: **Block 1 DONE sorry-free** (R17); **Block 2 DONE**
  (R30); **Block 3 DONE** — 3a `CJ_deriv`/`CJ_nonlift` (R13) + 3b
  `CJ_fprime`/`CJ_fiber` (R34), all S1; **Block 4a `CJ_witness_iff` +
  `fInt`/`fInt_eq` DONE** (R38); Block 4 remainder (mirror lemma,
  `f ↔ E₂` bridge, kernel verifier + `native_decide` anchor) not started.
- Watchdog: service `watch-cj` (`LANE=CJ proof/watch_lane.sh` →
  `pipeline/03-lean/CJ_watch.log`) still running — reuse it next
  session; it latches CONTENTION if the PDF lane compiles without a
  `CJ_inflight` marker (by design).

## What NOT to do

- Do not edit M1/PDF pipeline files, `HANDOFF.md`, or `lakefile.toml`
  (CJ compiles through `compile_lean.sh` without a lakefile entry;
  split into multi-module imports ONLY after a session that owns
  `lakefile.toml`).
- Do not mark the conjecture "proved": the cube-Wieferich slice is
  open beyond 2⁶⁴ and the finite screen (2.6×10⁶) is external evidence,
  not a theorem.
