# Mathlib API Lessons Learned

Hard-won knowledge for encoding elementary number theory proofs in Lean 4
+ Mathlib v4.35.0-rc2. Every item here cost real compilation time.

Companion doc: `pipeline/03-lean/ENCODING_MAP.md` — the author's notation →
Lean/Mathlib term mapping plus copy-paste proof patterns that already
compiled (this file = API pitfalls, that file = terminology + patterns).

## ZMod with a variable modulus `n : ℕ`

`ZMod n` is a field when `n` is prime, but Lean doesn't always resolve the
field instance for a *variable* `n : ℕ` with only `hn : Nat.Prime n` in
context. Specific issues:

| What you'd expect to work | What actually happens | Workaround |
|---|---|---|
| `linarith` on ZMod equations | **Fails.** `linarith` operates on linear arithmetic over `ℤ`/`ℕ`, not finite fields. | Convert ZMod equalities to `ℤ` divisibility via `ZMod.intCast_zmod_eq_zero_iff_dvd`, then use `omega` on `ℤ`. |
| `omega` on ZMod equalities | **Fails.** Same reason. | Same workaround: lift to `ℤ` first. |
| `mul_right_cancel₀ ha (h : a*c = b*c)` | **Fails:** missing `IsRightCancelMulZero (ZMod n)` instance. | Use `Field.mul_left_cancel₀` or `eq_of_mul_eq_mul_left` from the `Field` API. For a field, `a ≠ 0 → a * b = a * c → b = c` is available via `mul_left_cancel₀`. |
| `FiniteField.pow_card_sub_one_eq_one h2ne0` | **Type mismatch.** Verified at this pin (`#check @`): the signature is `(a : K) (ha : a ≠ 0) : a ^ (Fintype.card K - 1) = 1` for `[GroupWithZero K] [Fintype K]` — it takes an **element + nonzero proof**, NOT a unit. (An earlier note here claimed a unit; that was wrong. The unit-taking theorem is a different lemma: `ZMod.units_pow_card_sub_one_eq_one (a : (ZMod p)ˣ)`.) | Pass element and proof: `FiniteField.pow_card_sub_one_eq_one 2 h2ne0`. For `ZMod p` prefer **`ZMod.pow_card_sub_one_eq_one h2ne0`** (gives `a ^ (p - 1) = 1` directly, needs `Fact (Nat.Prime p)`) — no `Fintype.card` rewriting. |

## Exponentiation and `pow_mul`

`a ^ (m * n)` does **not** unify with `(a ^ m) ^ n` for rewriting. Lean
normalizes `m * n` but not the reversed `(a ^ m) ^ n` form. If you have
`h : a ^ (m * n) = ...` and want to rewrite the LHS as `(a ^ m) ^ n`:

```lean
-- WRONG: rewrite won't match
rw [show m * n = n * m from by omega, pow_mul] at h

-- RIGHT: use `calc` or `show` to align the term order first
have h' : a ^ (n * m) = ... := by rwa [mul_comm] at h
rw [pow_mul] at h'
```

Or use `← pow_mul` in the other direction. The key is that `pow_mul`
has a specific argument order; check with `#check @pow_mul`.

**Pin signature (Mathlib/Algebra/Group/Pow/Monoid.lean:459):**
`pow_mul (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n`. Both directions
were used at this pin:

| Goal shape | Use |
|---|---|
| have `hsol : u ^ (k * n) + …` , want `(u ^ k) ^ n + …` | `rw [pow_mul, pow_mul, pow_mul] at hsol` — `k * n` matches `?m * ?n` directly, NO `mul_comm` needed |
| have `h : (a ^ m) ^ n = …` , want `a ^ (m * n) = …` | `rw [← pow_mul] at h` |

(Bổ đề 2, L2/Basic.lean: one F2 round cost the wrong direction:
`rw [← pow_mul]` fails on `u ^ (k * n)` with "Did not find an occurrence
of the pattern `(?a ^ ?m) ^ ?n`".)

## Odd powers of negation

`Odd.neg_pow` has signature:

```lean
theorem Odd.neg_pow {R : Type*} [Ring R] {n : ℕ} (hn : Odd n) (a : R) :
    (-a) ^ n = -a ^ n
```

Usage: `rw [Odd.neg_pow hn2odd]` where `hn2odd : Odd (n-2)`.

**Pitfall:** this rewrites `(-a)^n` to `-(a^n)`, but if the term is
`(-b^n)^{n-2}`, Lean sees `(- (b^n))^{n-2}`, which is the correct form.
Make sure the negation is on the base, not inside a subtraction.

## `Int.ModEq` ↔ ZMod equality

The bridge between `Int.ModEq` (our hypothesis format) and ZMod equality
(what the proof needs):

```lean
-- Int.ModEq → ZMod equality
-- (a ≡ b [ZMOD n]) → ((a : ZMod n) = b)
-- For the 0 case use ONE of (both grep-verified at the pin, 2026-09-25):
--   CharP.intCast_eq_zero_iff (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a
--     (Mathlib/Algebra/CharP/Defs.lean:99; R = ZMod n, p = n)
--   ZMod.intCast_zmod_eq_zero_iff_dvd — EXISTS but takes explicit args
--     (`(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp`, Bernoulli.lean:626);
--     writing bare `.mp` fails with "Unknown constant …mp" (compile #1,
--     lines 52/77/83). Confirm arg list with one #check.
-- Or: norm_cast / exact_mod_cast for the general case

-- ZMod equality → Int.ModEq
-- ((a : ZMod n) = b) → (a ≡ b [ZMOD n])
-- Use: ZMod.intCast_eq_iff or norm_cast
```

**Tip:** `exact_mod_cast` and `norm_cast` can often close these gaps
automatically if the types line up.

## Reducing mod n² to mod n

If `h : a ≡ 0 [ZMOD n²]`, then `a ≡ 0 [ZMOD n]` since `n ∣ n²`.

**CORRECTED 2026-09-25 (compile #1 falsified the old recipe):**
`Int.ModEq.dvd` is NOT a modEq-transformer — Lean reports
`Function expected at Int.ModEq.dvd ?m … has type ? ∣ ? - ?`
(see `03-lean/L7-FRAG-01_compile_20260925.log`, line 96). The old snippet
below never actually compiled.

- Working building blocks (grep-verified at the pin this session):
  - `Int.modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ a - b` (used at
    `Mathlib/Algebra/CharP/Basic.lean:68`)
  - `Int.modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a`
    (`Mathlib/Data/Int/ModEq.lean:96`) — zero-form only.
- Intended replacement route (batched `#check` before first use):
  `Int.modEq_iff_dvd.mp h` gives `n² ∣ term − 0`; combine with
  `dvd_trans (dvd_pow_self …)` to get `n ∣ term`. Confirm exact
  `dvd_pow_self` signature in the same batch (its `(by omega)` argument
  misfired at compile #1 line 96).

## Fermat's Little Theorem in Mathlib

Verified at this pin (2026-09-25, `#check @` + local source
`Mathlib/FieldTheory/Finite/Basic.lean`):

- **`ZMod.pow_card_sub_one_eq_one {a : ZMod p} (ha : a ≠ 0) :
  a ^ (p - 1) = 1`** — the direct FLT lemma for `ZMod p`. Requires
  `Fact (Nat.Prime p)` (declared as `variable {p : ℕ} [Fact p.Prime]`),
  which also supplies the `Field (ZMod p)` instance. Prefer this.
- `FiniteField.pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) :
  a ^ (Fintype.card K - 1) = 1` — generic `GroupWithZero K` + `Fintype K`.
  Element + nonzero proof (NOT a unit). On `ZMod p` the exponent is
  `Fintype.card K - 1`, so it needs a `ZMod.card p` rewrite — that is
  exactly why the `ZMod` version above exists.
- `ZMod.units_pow_card_sub_one_eq_one (p) [Fact p.Prime]
  (a : (ZMod p)ˣ) : a ^ (p - 1) = 1` — unit-based form; only when you
  already have a `Units` element.
- For concrete `p` (e.g., `ZMod 7`), `decide` / `norm_num` may close it.

For a **variable** prime `p`, the FLT proof needs:
1. `Fact (Nat.Prime p)` in the context (or pass `hn` explicitly).
2. A `Field (ZMod p)` instance (follows from `Fact (Nat.Prime p)`).
3. Statement shape `a ≠ 0 → a ^ (p - 1) = 1` → apply
   `ZMod.pow_card_sub_one_eq_one`.

## `char_p` and `ZMod`

`CharP.intCast_eq_zero_iff` exists in `Mathlib.Algebra.CharP.Defs`:

```lean
theorem intCast_eq_zero_iff (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a
```

where `R` has `CharP R p`. For `R = ZMod n`, this gives
`(a : ZMod n) = 0 ↔ (n : ℤ) ∣ a` when `n` is the characteristic.

**Pitfall:** the `p` in `CharP R p` is the `ringChar`, which equals `n`
only when `n` is prime. For composite `n`, `CharP (ZMod n) n` still holds
(definitionally), but the field instance doesn't.

## Session 2026-09-25 — L2-01 (bổ đề 2) — all steps S1

Verified at this pin by compile (`03-lean/L2-01_compile_20260925.log`,
final file: `03-lean/L2/Basic.lean`). The chunk is a pure exponent
identity + contrapositive wrap — no ZMod, no divisibility.

1. **`pow_mul` direction is the only trap.** Goal
   `(u ^ k) ^ n + (v ^ k) ^ n = (t ^ k) ^ n` from
   `hsol : u ^ (k * n) + v ^ (k * n) = t ^ (k * n)`:
   `rw [← pow_mul]` FAILS ("Did not find an occurrence of `(?a ^ ?m) ^ ?n`").
   The pin signature is `pow_mul (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n`
   (Mathlib/Algebra/Group/Pow/Monoid.lean:459), so the working direction
   is plain `rw [pow_mul, pow_mul, pow_mul] at hsol`. `k * n` matches
   `?m * ?n` directly — the `mul_comm` I added first was redundant.
2. **Nonzero preservation:** `u ≠ 0 → u ^ k ≠ 0` is `pow_ne_zero k hu`.
3. **Contrapositive assembly:** `intro h` on the `¬ ∃` conclusion,
   `obtain ⟨u, v, t, hu, hv, ht, hsol⟩ := h`, feed the step theorem,
   `exact hno ⟨u ^ k, v ^ k, t ^ k, …⟩`. The carried hypotheses `n ≥ 3`
   and `k ≠ 0` are unused and must be named `_hn`/`_hk` (linter), exactly
   the L1 `_hn` pattern.
4. **Cost:** two clean `import Mathlib` round-trips measured 149 s
   (failed direction) and 196 s / 311 s (successes) under no contention;
   evidence log plus `#print axioms` in `L2-01_compile_20260925.log`.

## Session 2026-09-25 — L7-FRAG-01 compile #1 (whole batch = F2)

Full evidence: `03-lean/L7-FRAG-01_compile_20260925.log`. All items below
are representation/API problems; no author step was mathematically rejected.

1. **Prefix `-` vs `^` precedence — suspect #1 for four failures.**
   `(-(b : ZMod n) ^ n) ^ (n - 2)` did NOT match `Odd.neg_pow`'s pattern
   `(-?a) ^ (n - 2)` ("Did not find an occurrence", lines 145/187/215/219)
   — evidence the term elaborates as `((-b) ^ n) ^ (n - 2)`, i.e. prefix
   negation binds tighter than `^` here. **Always write the intended form
   explicitly** (`(-((b : ZMod n) ^ n)) ^ (n - 2)`) and confirm precedence
   with a one-line `#check` before batch use.
2. `Nat.Prime.eq_two_or_odd` returns `n % 2 = 1`, NOT `Odd n`
   (line 118). Bridge explicitly (e.g. `⟨n / 2, by omega⟩`-style) after
   checking the real `Odd` introduction lemma.
3. `simpa using (h : -0 + 3 = 0)` did NOT produce `3 = 0` (line 74).
   Use explicit `rw [neg_zero, zero_add] at h` or `ring_nf at h`.
4. `ring` leaving trivial-looking goals inside `calc` steps: each `calc`
   line must CLOSE its step — `rw [...]` alone leaves an unsolved goal
   (lines 131/156). Append `; ring` inside the step tactic.
5. `have … := by rw [hstep]; ring` ordering bug: `hpow` was used before
   its definition (line 169 `Unknown identifier hpow`) — declaration
   order matters even for same-block helpers.
6. `pow_eq_zero` is an unknown identifier at this pin (line 196) — find
   the real name (`pow_eq_zero_iff` / `pow_eq_zero` variants) by local
   grep + batched `#check`.
7. Conclusion-factor order: product splits as `↑c ^ n + ↑b ^ n` but the
   author's hypothesis is `↑b ^ n + ↑c ^ n` (line 264) — `add_comm` at
   the callsite.
8. Whole-product cast: `rw [ZMod.intCast_zmod_eq_zero_iff_dvd]` missed a
   partially-cast goal (line 253) — cast the Int product first with
   `show`/`exact_mod_cast`, then rewrite the dvd form.
9. `ZMod n` numerals displayed as `↑n ^ 2` in `h1`'s modulus: statement
   uses `(n ^ 2 : ℤ)` = `(↑n) ^ 2`; keep that spelling consistent in
   bridges.
10. `by omega` as `(dvd_pow_self (n : ℤ) (by omega))`'s side goal failed
    with a `% ↑n` counterexample (line 96) — the argument is not the
    `2 ≠ 0` expected; batched `#check @dvd_pow_self` decides.

## Session 2026-09-25 — L1-01 (bổ đề 1) — all six steps S1

Verified at this pin by compile (`03-lean/L1-01_compile_20260925.log`,
final file: `03-lean/L1/Basic.lean`) unless marked "grep-only". Term
mapping and reusable proof patterns for the next chunks:
`pipeline/03-lean/ENCODING_MAP.md`.

1. **`Int.gcd` is ℕ-valued; nesting needs an explicit cast.**
   `Int.gcd u (Int.gcd v t)` does not typecheck — the second argument is
   `ℤ`. Write the triple gcd as
   `Int.gcd u ((Int.gcd v t : ℕ) : ℤ)`. `(x,y,z) = 1` (no common divisor)
   is exactly this nested form `= 1`.
2. **Divisibility of a gcd, both directions (confirmed by `#check @`):**
   - `Int.gcd_dvd_left (a b : ℤ) : ↑(a.gcd b) ∣ a` (same for `_right`) —
     note the `↑` (the gcd is a `ℕ`).
   - `Int.dvd_gcd : ↑c ∣ a → ↑c ∣ b → c ∣ a.gcd b` — **ℤ divisibility in,
     ℕ divisibility out**; that asymmetry is the useful one for
     "gcd is greatest".
   - `Int.dvd_coe_gcd : c ∣ a → c ∣ b → c ∣ ↑(a.gcd b)` — ℤ→ℤ form.
3. **Maximality recipe that worked** (proving "divide by a triple gcd ⇒
   coprime"): build `hmax : ∀ m : ℕ, (m:ℤ) ∣ u₀ → (m:ℤ) ∣ v₀ → (m:ℤ) ∣ t₀
   → m ∣ D` by `Int.dvd_gcd` twice; then show `e * d` is again a common
   divisor (`obtain ⟨s, hs⟩ := h`, then `push_cast; ring`) so `e * d ∣ d`,
   cancel `d ≠ 0` and finish with `Nat.dvd_one.mp`.
4. **`Dvd` unfolds to `∃ c, b = a * c`** — `obtain ⟨u, hu⟩ := h` with
   `h : (d:ℤ) ∣ u₀` gives `hu : u₀ = ↑d * u` directly. No need to guess
   `exists_eq_mul_left_of_dvd`; watch the **argument order** (multiple on
   the right, `u₀ = ↑d * u`, the author writes `u₀ = u·d` — swap with
   `mul_comm`).
5. **`zero_dvd_iff : 0 ∣ a ↔ a = 0`** exists, but after `rw [h0] at h` you
   get `↑(0:ℕ) ∣ a`, which is not syntactically `(0:ℤ) ∣ a` — insert
   `have : (0:ℤ) ∣ a := by simpa using h` first.
6. **Cancellation for `ℤ` and `ℕ`:** `mul_left_cancel₀ (ha : a ≠ 0)`,
   `mul_right_cancel₀ (hb : b ≠ 0)` — both synthesize for `ℤ` and `ℕ`
   (`IsLeftCancelMulZero`/`IsRightCancelMulZero` instances exist).
7. **`rw [← h]` fails on associativity/commutativity shape mismatches.**
   With `hk : D = e * D * k` and goal `e * k * D = D`, `rw [← hk]` errors
   ("did not find an occurrence of `e * D * k`"). Use
   `calc e * k * D = e * D * k := by ring` / `_ = D := hk.symm`.
   `ring` handles `ℕ` as well as `ℤ`.
8. **`set x : α := e with hx`** makes every goal occurrence definitionally
   `x`; `rw [hx]` then gives the expanded form, and `simpa only [hx] using
   h` converts a hypothesis back. This is the clean way to keep triple-gcd
   goals readable.
9. **`pow_dvd_pow_of_dvd (h : a ∣ b) (n : ℕ) : a ^ n ∣ b ^ n`**
   (`Mathlib/Algebra/Divisibility/Basic.lean:269`, `[CommMonoid α]`).
   NB `pow_dvd_pow` is a *different* lemma (`a : α`, `h : m ≤ n`,
   `a ^ m ∣ a ^ n`) — using it for `a^n ∣ b^n` fails.
10. **No `pow_dvd_pow_iff_left` for ℤ/ℕ at this pin** (grep: the only
    `pow_dvd_pow_iff` is `IntegrallyClosed`-scoped). For
    `a ^ n ∣ b ^ n ⟹ a ∣ b` (author step S4) the available route is
    `Nat.factorization_le_iff_dvd` + `Nat.factorization_pow`
    (`factorization (n ^ k) = k • n.factorization`, `Data/Nat/Factorization/Defs.lean:183`)
    + `Nat.le_of_mul_le_mul_left` (or `nsmul_le_nsmul_iff_left`) pointwise.
    **This step is NOT valid for `n = 0`** (`a^0 = 1 ∣ b^0 = 1` while
    `a ∤ b`), so `n ≠ 0` must be supplied — it follows from the author's
    `n ≥ 3`, i.e. it is an F3 side condition, not a new assumption.
11. **Cost note:** one `lake env lean` round-trip on a warm `import Mathlib`
    file measured **288–387 s** this session (contended container). Batch
    every probe into one file; do not spend a round-trip per name.

### L1-01 continued (steps S4/S5/S6 + assembly, all S1)

12. **`Int.dvd_gcd` vs `Int.dvd_coe_gcd` — ℕ out vs ℤ out.** Both exist and
    the wrong one fails with a bare type mismatch:
    - `Int.dvd_gcd : ↑c ∣ a → ↑c ∣ b → c ∣ a.gcd b` — conclusion is **Nat**
      divisibility.
    - `Int.dvd_coe_gcd : c ∣ a → c ∣ b → c ∣ ↑(a.gcd b)` — conclusion is
      **ℤ** divisibility (this is the one to chain when the goal is
      `↑d ∣ ↑(gcd …)`).
13. **`zero_pow_succ` does not exist at this pin** (`unknown identifier`).
    To see `(0 : ℕ) ^ (m+1) = 0`, use core `pow_succ` then `mul_zero`:
    `rw [hd, pow_succ, mul_zero, zero_dvd_iff] at hN`. Get the `m+1` shape
    from `Nat.exists_eq_succ_of_ne_zero hn` (`hn : n ≠ 0`).
14. **Working recipe for `d ^ n ∣ t ^ n → d ∣ t` (`[CommMonoid]`-free case).**
    No `pow_dvd_pow_iff_left` for ℤ/ℕ at this pin; the route that compiled:
    ```lean
    have hN : d ^ n ∣ t.natAbs ^ n := by
      have h' := (Int.natAbs_dvd_natAbs).mpr h
      simpa only [Int.natAbs_pow, Int.natAbs_natCast] using h'
    -- then, with hd : d ≠ 0 and hB : t.natAbs ≠ 0:
    have h1 : (d ^ n).factorization ≤ (t.natAbs ^ n).factorization :=
      (Nat.factorization_le_iff_dvd (pow_ne_zero n hd) (pow_ne_zero n hB)).mpr hN
    simp only [Nat.factorization_pow] at h1
    simp only [Finsupp.le_def] at h1 ⊢
    intro p
    have hp := h1 p
    simp only [Finsupp.smul_apply, nsmul_eq_mul] at hp
    exact Nat.le_of_mul_le_mul_left hp (Nat.pos_iff_ne_zero.mpr hn)
    ```
    Lift back with `(Int.natAbs_dvd_natAbs).mp (by simpa only
    [Int.natAbs_natCast] using hdvd)`. Note `Int.natAbs_dvd_natAbs` is used
    **both ways** in this project: `.mpr` to go ℤ→ℕ, `.mp` to go ℕ→ℤ.
    `Int.dvd_one`-style wrappers are not needed: `Nat.dvd_one.mp` +
    `Int.natCast_dvd_natCast.mp` finish `↑d ∣ (1:ℤ) → d = 1`.
15. **Symmetric instances of a `dvd_pow` template need `dvd_sub` + `dvd_neg`.**
    For the author's "chứng minh tương tự" the third coordinate came from
    `t ^ n - u ^ n = v ^ n` (`rw [← hsol]; ring`) and `v ^ n - t ^ n = -(u ^ n)`
    with `(dvd_neg.mp h)`; `dvd_sub : a ∣ b → a ∣ c → a ∣ b - c` is core.
16. **`Nat.exists_eq_succ_of_ne_zero`** is the standard way to trade `n ≠ 0`
    for a `m+1` shape (`Data/Int/GCD.lean:57` uses it); it substitutes with
    `obtain ⟨m, rfl⟩`.
17. **Unused-hypothesis linter:** an author hypothesis carried for
    faithfulness but not used by a step triggers
    `Variable name ... is not explicitly referenced`. Name it `_hn` and
    explain in the docstring rather than dropping it (dropping would
    misrepresent the author's stated hypotheses).

## Session 2026-09-26 — L3-01 (bổ đề 3) — all steps S1

Verified at this pin by compile (`03-lean/L3-01_compile_20260926.log`,
final file: `03-lean/L3/Basic.lean`). The chunk is gcd/divisibility algebra
over ℤ; these are the API facts that did the work.

1. **`Int.exists_gcd_one` is the author's whole S0 sentence.** At
   `Mathlib/Data/Int/GCD.lean:203`:
   `Int.exists_gcd_one {m n : ℤ} (H : 0 < Int.gcd m n) :
   ∃ m' n' : ℤ, Int.gcd m' n' = 1 ∧ m = m' * ↑(Int.gcd m n) ∧ n = n' * ↑(Int.gcd m n)`
   — the witnesses are the quotients `m / ↑(m.gcd n)`, `n / ↑(m.gcd n)`
   (`Int.ediv_mul_cancel`), i.e. exactly the author's `a_1`, `c'_2`; the
   `↑` on the gcd is inserted automatically (Int.gcd is ℕ-valued).
   Positivity of the gcd: `Int.gcd_def` (`gcd i j = Nat.gcd i.natAbs
   j.natAbs`, `:159`, `:= rfl`) plus
   `Nat.gcd_pos_of_pos_left c.natAbs (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha))`.
   There is **no** `Int.natAbs_pos`; the idiom is
   `Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr h)`.
2. **Rewriting `a` / `c` when the goal still contains `Int.gcd a c`
   mangles the goal.** `rw [h]` with `h : a = …` (or `c = …`) rewrites
   *every* occurrence, including the `a` inside the `Int.gcd a c`
   argument, producing nonsense such as `Int.gcd (↑(a.gcd c) * a1) c`.
   Two fixes that compiled:
   - write the proof so the rewrite is unnecessary, e.g.
     `calc a = a1 * ↑(Int.gcd a c) := h1; _ = ↑(Int.gcd a c) * a1 := mul_comm _ _`;
   - or target one occurrence: `conv_lhs => rw [h2]`, `conv_rhs => rw [ha_fin]`.
   This cost two full compile round-trips (S0 round 1; S1+S2 round 3).
   Read the log with care: round 3's *reported* message is a `mul_assoc`
   pattern miss — a symptom. The cause was the earlier `rw` in the same
   tactic block, which had already mangled the goal's gcd argument.
3. **`mul_assoc` reassociates leftwards**: its statement is
   `(a*b)*c = a*(b*c)`, so to turn `g * (g^(n-1) * x)` into
   `(g * g^(n-1)) * x` the rewrite is `rw [← mul_assoc]`; plain
   `rw [mul_assoc]` fails with "Did not find an occurrence of the pattern
   `?a * ?b * ?c`". Then `rw [← pow_succ']` folds `g * g^(n-1)` into
   `g^((n-1)+1)` and `Nat.sub_add_cancel (by omega)` turns that into `g^n`.
   Pin facts: `pow_succ' (a : M) : ∀ n, a^(n+1) = a * a^n`
   (`Mathlib/Algebra/Group/Monoid.lean:419`); `pow_mul :
   a^(m*n) = (a^m)^n` (used `←` to fold `(g^(n-1))^n` into `g^((n-1)*n)`).
   This cost one compile round-trip (S1+S2 round 4).
4. **Int gcd ↔ `IsCoprime` bridge + Euclid.** `Int.isCoprime_iff_gcd_eq_one
   {m n : ℤ} : IsCoprime m n ↔ Int.gcd m n = 1`
   (`Mathlib/RingTheory/Coprime/Lemmas.lean:38`). With it:
   - `IsCoprime.dvd_of_dvd_mul_left (H1 : IsCoprime x y) (H2 : x ∣ y*z) : x ∣ z`
     and the `_right` version (`Mathlib/RingTheory/Coprime/Basic.lean:100/105`)
     are Euclid's lemma — the author's "`(c'_1,b) = 1`, hence `c'_2^n = k·b`";
   - `IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x^m) (y^n)`, plus
     `.pow_left` / `.pow_right` (`…/Coprime/Lemmas.lean:196–205`) — the
     author's `(a_1,c'_2) = 1 ⟹ (a_1^n,c'_2^n) = 1`.
   `Int.gcd_comm` flips argument order when the bridge lands reversed.
5. **`(c'_1,b) = 1` from `(a,b) = 1` and `c'_1 ∣ a`**: `Int.dvd_gcd`
   (ℕ-out) closes it, e.g.
   `have h := Int.dvd_gcd hm_a hm_b; simpa only [hgcd_ab] using h`,
   with `hm_a : ↑m ∣ a` from `dvd_trans (Int.gcd_dvd_left _ b) hg_dvd_a`.
6. **`|k| = 1` is cleanest through `IsUnit`.** `Int.isUnit_iff_natAbs_eq :
   IsUnit u ↔ u.natAbs = 1` (`Mathlib/Algebra/Group/Int/Units.lean:76`),
   then `Int.isUnit_mul_self (hu : IsUnit u) : u * u = 1` (`:83`) and
   `Int.eq_one_or_neg_one_of_mul_eq_one (h : u*v = 1) : u = 1 ∨ u = -1`
   (`:51`). The odd-power step is
   `Odd.neg_one_pow (h : Odd n) : (-1 : α)^n = -1`
   (`Mathlib/Algebra/Ring/Parity.lean:191`, `@[simp]`).
   `k ∣ 1` route: `Int.dvd_coe_gcd h7 h8 : k ∣ ↑(Int.gcd …)` (ℤ-out),
   rewrite by `Int.gcd … = 1`, then `(Int.natAbs_dvd_natAbs).mpr` (ℤ→ℕ)
   + `Nat.dvd_one.mp`.
7. **Misc confirmed at this pin:** `dvd_pow (hab : a ∣ b) (hn : n ≠ 0) :
   a ∣ b^n` (`Mathlib/Algebra/Divisibility/Basic.lean:189`);
   `dvd_mul_of_dvd_left (h : a ∣ b) (c) : a ∣ b * c` (`:83`);
   `dvd_mul_right (a b) : a ∣ a * b` (`:80`); `pow_ne_zero`; `mul_ne_zero`;
   `mul_left_cancel₀` / `mul_right_cancel₀`; `Nat.dvd_one.mp`;
   `dvd_trans`; `Dvd` witness form `⟨w, (h : b = a * w)⟩`.
8. **`Odd n` does not hand you `0 < n`**: the author's "odd positive
   integer" is carried as two binders — `hn : Odd n` (for `Odd.neg_one_pow`)
   and `hn0 : 0 < n` (for `Nat.sub_add_cancel`, and `hn0.ne'` for
   `dvd_pow`).
9. **Cost:** 11 compile round-trips (~150–350 s each warm) for 8 step
   declarations + assembly. Of those, **three failed rounds, all F2**
   (round 1 = S0; rounds 3 and 4 = S1+S2 — the traps in items 2 and 3),
   plus one round that compiled but reported the unused-`hb` linter
   warning (fixed in the next round). No F1/F3/F4 outcome occurred.

## Session 2026-09-26 — L4-01 (bổ đề 4), DONE (all six declarations S1)

State: `03-lean/L4/Basic.lean` compiles EXIT:0, zero warnings, zero `sorry`;
`#print axioms` on `L4_step_S1_S2`, `L4_step_S3`, `L4_step_S4`,
`L4_step_S5`, `L4_step_S6` and the assembly `L4_bo_de_4` = propext,
Classical.choice, Quot.sound only. Eleven rounds: 2 probe rounds pinned every
name below before the first step, 6 author-step rounds, and 4 F2 rounds —
every F2 tactic/API shape, no F1/F3/F4. Per-round diagnosis:
`03-lean/L4-01_compile_20260926.log`. Step table, reusable signatures and
patterns P12/P13: `ENCODING_MAP.md` §B Chunk L4-01.

1. **`Int.pow_dvd_pow_iff` EXISTS** —
   `∀ {a b : ℤ} {n : ℕ}, n ≠ 0 → (a ^ n ∣ b ^ n ↔ a ∣ b)`. The L1 session's
   item 10 above ("No `pow_dvd_pow_iff_left` for ℤ/ℕ at this pin") is too
   strong: the ℤ form is there. L1's own proof routes through
   `Nat.factorization` and is unaffected.
2. **`Int.Prime.dvd_pow' {n : ℤ} {k p : ℕ} (hp : Nat.Prime p)
   (h : (p : ℤ) ∣ n ^ k) : (p : ℤ) ∣ n`** — the ℤ-output prime-power step,
   taking `Nat.Prime p` directly, so no `Prime (p : ℤ)` bridge is needed
   (`Int.Prime.dvd_pow` is the ℕ-output / `natAbs` variant).
3. **An m-adic decomposition of a ℤ number**: Mathlib has no ℤ version, but
   `Nat.exists_eq_pow_mul_and_not_dvd (hn : n ≠ 0) (p) (hp : p ≠ 1) :
   ∃ e n', ¬p ∣ n' ∧ n = p ^ e * n'` does the work on `z.natAbs`. Transport
   back by destructuring `(m : ℤ) ^ s ∣ z`, obtained from the ℕ
   decomposition with `Int.natCast_dvd.mpr` (`↑m ∣ n ↔ m ∣ n.natAbs`) plus
   `simpa only [Nat.cast_pow]`; maximality of `s` gives `m ∤ r` (via
   `r.natAbs = R`, cancelling `m ^ s ≠ 0`). The generic
   `FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd` is the alternative
   when a `FiniteMultiplicity` instance is already in context.
4. **Comparing m-adic exponents without valuations** (the S5 shape): from
   `m ^ 2 ∣ (m ^ s * R) ^ n` with `¬m ∣ R`, cancel `R ^ n` by coprimality —
   `(hm.coprime_iff_not_dvd.mpr hR).pow 2 n` gives `Nat.Coprime (m^2) (R^n)`,
   then `Nat.Coprime.dvd_of_dvd_mul_right` — and finish with
   `Nat.pow_dvd_pow_iff_le_right hm.one_lt :
   (m ^ 2 ∣ m ^ (s * n) ↔ 2 ≤ s * n)`. This needs no `Finsupp`-level
   `factorization` computation at all. Names used:
   `Nat.Prime.coprime_iff_not_dvd`, `Nat.Coprime.pow`,
   `Nat.Coprime.dvd_of_dvd_mul_right`, `Nat.pow_dvd_pow_iff_le_right`.
5. **Two slips that cost the L4 F2 round (round 4)** — both pure shape, no
   change of statement or inference:
   - after `rw [h, mul_zero] at h`, the hypothesis IS `c.natAbs = 0`, so
     `hC0 h` is right and `hC0 h.symm` is a type error;
   - `Int.natAbs_dvd_natAbs : a.natAbs ∣ b.natAbs ↔ a ∣ b`, so the ℤ→ℕ
     direction is **`.mpr`** and ℕ→ℤ is `.mp` (L1's item 14 says the same —
     it is still easy to reach for `.mp` first).
6. `Nat.factorization_self` does **not** exist (probe-confirmed); the useful
   companions are `Nat.Prime.factorization_pow`
   (`(p ^ k).factorization = fun₀ | p => k`) and the already-known
   `Nat.factorization_pow_self`.
7. **The `Int.gcd` rewrite trap also bites from the OTHER side of the goal**
   (L4 rounds 6–7; L3's items 2–3 cover the case where the goal itself
   contains the gcd). If the goal is `LHS = RHS` and `RHS` mentions
   `Int.gcd x y` while the rewrite substitutes `x` or `y`, a plain `rw`
   rewrites *inside* the gcd argument. Relaying a witness for
   `a = (m:ℤ)^k * l` with `hl' : l = ↑(Int.gcd h l) * l'`, the step
   `(m:ℤ)*(m:ℤ)^j * l = (m:ℤ)*(m:ℤ)^j * (↑(Int.gcd h l) * l')` by
   `rw [hl']` produces
   `… = ↑m * ↑m ^ j * (↑(Int.gcd h (↑(Int.gcd h l) * l')) * l')`.
   Remedy: `conv_lhs => rw [hl']` (or `conv_rhs`). General rule for this
   project: **never `rw` a hypothesis whose variable occurs as an `Int.gcd`
   argument** — either avoid the rewrite (`calc` + `push_cast` + `ring`) or
   confine it with `conv`. Six occurrences across L3 rounds 1/3 and L4
   rounds 6/7.
8. **Exponent comparison has two routes; item 4 above is only one of them.**
   L4's S5 ended up using the *factorization* route, and it is the better one
   whenever the equation must be transported to `ℕ` anyway: for prime `m` and
   `m ∤ X`, `(m ^ a * X).factorization m = a` is a short local fact
   (`Nat.factorization_mul`, `Finsupp.add_apply`,
   `Nat.factorization_pow_self`, `Nat.factorization_eq_zero_of_not_dvd`), and
   two `rw` steps then compare the two sides' `natAbs` factorizations at `m`.
   The coprime route of item 4 (`Prime.coprime_iff_not_dvd` + `Coprime.pow` +
   `dvd_of_dvd_mul_right` + `Nat.pow_dvd_pow_iff_le_right`) is better when
   everything already lives in `ℕ` — it is what `L4_step_S3` uses for
   `2 ≤ n·s`, where no transport is involved.

## Session 2026-09-26 — L5-01 (bổ đề 5), DONE (all 21 declarations S1)

State: `03-lean/L5/Basic.lean` compiles EXIT:0, zero warnings, zero `sorry`;
`#print axioms` on `L5_step_S2` … `L5_step_S18`, the assembly `L5_bo_de_5` and
the three helpers = propext, Classical.choice, Quot.sound only. Twenty-nine
rounds: one batched probe round (`#check @` list, which also caught the
`∑ i ∈ s` notation), then 28 compiles of the file — 17 green on the first try
and **10 repaired, every repair an F2 shape (no F1/F3/F4)** — plus one green
round with two unused-`simp` warnings that the next round removed.
Per-round diagnosis: `03-lean/L5-01_compile_20260926.log`. Step
table, reusable signatures and patterns P14–P18: `ENCODING_MAP.md` §B Chunk
L5-01.

1. **A printed division can be avoided by proving the identity in `ℤ[X]`.**
   S3's `A = Σ_k (−1)^kC_n^k(u+v)^{n−1−k}v^k` is the author's "mà u+v ≠ 0,
   nên …", and dividing is illegitimate in b)–d) where `u+v` may vanish. Both
   sides satisfy `(X + C v)·Y = X^n + (C v)^n` by S2 — stated *generically*
   over `CommRing R`, so it instantiates at `ℤ[X]` — hence `(X + C v)·(A−B)
   = 0`, `mul_eq_zero.mp` plus `Polynomial.X_add_C_ne_zero v` give `A = B` as
   polynomials, and `congrArg (Polynomial.eval u)` + `unfold A B` +
   `Polynomial.eval_finsetSum` + `simpa` transfers to `ℤ`. One round, no index
   arithmetic.
2. **`CharP.intCast_eq_zero_iff` takes `R` and `p` explicitly** (binders
   `variable (R : Type*)` outside the namespace and `(p : ℕ)`): the call is
   `CharP.intCast_eq_zero_iff (ZMod n) n x`; passing only `x` fails with
   "expected `Type`". It is the bridge `(x : ZMod n) = 0 ↔ n ∣ x`.
3. **`omega` does not do nested `Nat` subtraction.** Both `n - 1 - (i+1) =
   n - 1 - 1 - i` and `n - 1 - k = (n - 2 - k) + 1` failed with "No usable
   constraints found", while `Nat.sub_succ' (m n) : m - n.succ = m - n - 1`,
   `Nat.sub_right_comm`, `Nat.sub_add_comm (h : k ≤ n) : n + m - k = n - k + m`
   and `Nat.sub_one_add_one_eq_of_pos` closed them in one or two `rw`s.
   `Nat.sub_succ` is the **`.pred`** variant (`n - (k+1) = (n-k).pred`).
4. **`Int.Prime.dvd_pow'` needs its exponent** (`(k := n)`); without it the
   elaborator cannot synthesize `k` from the divisibility hypothesis.
5. **The `Int.gcd_add_mul_*` shift lemmas are order-sensitive**:
   `m.gcd (n + m*k) = m.gcd n` (`_left_right`) versus `m.gcd (n + k*m) =
   m.gcd n` (`_right_right`). So in `A = (u+v)·B′ + n·v^{n−1}` the non-multiple
   summand must come first — state the decomposition as `n·v^{n−1} + (u+v)·B′`.
6. **`sub_zero` may fail to match a printed `- 0` in `ZMod n`** ("Did not find
   an occurrence of the pattern `?a - 0`" though the target printed exactly
   that). Going through a separately stated equality and finishing with `ring`
   (which normalizes the numerals) works.
7. **Prop-valued local instances: `have` over `haveI`.** `linter.style.haveILetI`
   fires on `haveI : Fact (Nat.Prime n) := ⟨hn⟩`; plain `have : Fact (Nat.Prime
   n) := ⟨hn⟩` still registers for instance search (Mathlib uses that form 82
   times) and keeps the file warning-clean.
8. **`nonneg_of_mul_nonneg_left` wants the positive factor on the right**:
   `0 ≤ k * n`, with `0 < n` supplied second.
9. **`Finset.sum_range_succ'` peels the *first* term** (`∑ k ∈ range (n+1), f k
   = ∑ k ∈ range n, f (k+1) + f 0`), `Finset.sum_range_succ` the last. The
   choice matters: the peeled index spelling and the *unfolded* spelling of the
   same exponent must agree syntactically for `ring` to see one atom.
10. **`Nat.Prime.dvd_choose_self (hk : k ≠ 0) (hk' : k < p)`** is the
    `C_n^k ⋮ n` source; `Int.prime_dvd_pow_sub_one`/`Int.ModEq.pow_card_sub_one
    _eq_one` (both taking `IsCoprime n ↑p`) are the ℤ FLT forms — the first for
    `u^{n−1} = 1 + mn`, the second for the `≡` statement.
11. **Cost:** 29 rounds at 374–415 s each (single container, no contention),
    8 of them F2 repairs; the batched probe round pinned every name that a
    local grep could not settle.

## Session 2026-09-26 — L6-01 (bổ đề 6): 13 compile rounds, 35 declarations

1. **`rw` rewrites ALL occurrences — and re-descends into the terms it just
   created.** `rw [one_pow]` on `1^n + 1^n = t^n` consumes *both* `1^n`, so a
   second `rw [one_pow]` errors with "Did not find an occurrence of the
   pattern". Same for `mul_pow` (one call normalises `(n^s*(c*c'))^n` all the
   way to `(n^s)^n * (c^n * c'^n)`), and for `rw [hexp]` when the goal contains
   both `n*s-1` and `n*s-1-2` (the second gets mangled:
   `n*s-1+1-1`). When only *one side's exponent* may move, use `conv`:
   `conv_lhs => rw [← …]` / `conv_rhs => rw [← pow_add]`.
2. **Exponent identities.** `(a^m)^n → a^(m*n)` is `← pow_mul`;
   `a^m * a → a^(m+1)` is `← pow_succ` (`pow_succ` is `a^(n+1) = a^n * a`);
   `a * a^m → a^(m+1)` is `← pow_succ'`. `pow_add` will **not** match a bare
   `n^s * n` (the second factor is not syntactically a power).
3. **`omega` cannot see products.** `n ≥ 3`, `s ≥ 1` give it nothing about the
   atom `n*s`, so `n*s-1 = s + (n*s-1-s)` is unprovable for it; feed the bound
   explicitly — `have hbnd : s + 2 ≤ n * s := by nlinarith [hn3, hs1]`, then
   `omega`. Also: `Nat.Prime n` alone gives only `2 ≤ n` (`omega` does pick
   that up), and `Odd n` alone gives only `1 ≤ n` (`Odd 1` is true), so
   `3 ≤ n` needs both: `have h2 := hn.two_le; obtain ⟨j, hj⟩ := hodd; omega`.
4. **FLT without `ZMod`: `Int.ModEq.pow_prime_eq_self`.** For "`n ∣ t` ⇒
   `n ∣ u+v`" (bổ đề 6 S15) the `ZMod` route is structurally blocked — the
   exponent and the modulus are the *same* variable, so
   `conv_lhs => rw [← Nat.sub_one_add_one_eq_of_pos hn.pos]` on
   `(u : ZMod n) ^ n` dies with "motive is not type correct ... Fact (Nat.Prime
   _a)". `Int.ModEq.pow_prime_eq_self hn u : u^n ≡ u [ZMOD ↑n]` needs no
   coprimality and stays in ℤ:
   `(Int.ModEq.pow_prime_eq_self hn u).add (…)`, then
   `hadd.symm.trans (by rw [Int.modEq_zero_iff_dvd]; exact h1)` and
   `(Int.modEq_zero_iff_dvd).mp hzero`.
5. **ℤ vs ℕ ne-zero in `pow_ne_zero`.** `pow_ne_zero e hn.ne_zero` has type
   `n^e ≠ 0` in ℕ; when the expected type is `(↑n)^e ≠ 0` (e.g. the argument of
   `Int.mul_dvd_mul_iff_left`) it is a type mismatch — use a ℤ proof:
   `have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne_zero`.
6. **`Nat.exists_eq_pow_mul_and_not_dvd` recipe** (maximal `n`-power of an
   integer `X ≠ 0`): apply it to `X.natAbs` with `p := n`, `p ≠ 1` proved by
   `hn.one_lt.ne'`; get `(n:ℤ)^e ∣ X` back with
   `Int.natCast_dvd.mpr ⟨R, hXR⟩` + `simpa only [Nat.cast_pow]`; transport the
   cofactor with `rw [hr, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]`
   and `mul_left_cancel₀` (which works on ℕ); `¬(n:ℤ) ∣ r` follows from
   `hR : ¬ n ∣ R` by `hrabs ▸ Int.natCast_dvd.mp hd`; `s ≥ 2` from `n² ∣ X`
   by *coprime cancellation* (`Nat.Coprime (n^2) r.natAbs` then
   `dvd_of_dvd_mul_right`) plus `Nat.pow_dvd_pow_iff_le_right hn.one_lt`.
7. **`Int.gcd x (x ^ (n-1)) = x.natAbs` for `n ≥ 2`** (the step that turns
   `a' = a^{n−1}` and `(a,a') = 1` into `a.natAbs = 1`): `Int.gcd_mul_left x 1
   (x^(n-2))` + `Nat.gcd_one_left`. Do **not** write `rw [hsplit, ← mul_one x,
   Int.gcd_mul_left]` — `← mul_one x` rewrites *every* `x`, including inside
   `x^(n-2)`; bind `Int.gcd_mul_left` first and rewrite in the hypothesis.
8. **`convert h using 1` can close the goal itself**, leaving the follow-up
   `ring` with "No goals to be solved". Prefer a named identity:
   `have hring : …= c' := by ring; rwa [hring] at h`.
9. **`Int.gcd_add_mul_left_left (m n k) : (n + m*k).gcd m = n.gcd m`**,
   `_right_left : (n + k*m).gcd m = n.gcd m` — so the *non-multiple* summand
   must be written first; to shift `N*x^(n-1) − x'` by the gcd of `x`, pass
   `k := N * x^(n-2)`.
10. **Simple divisibility witnesses: use `dvd_mul_of_dvd_left/right`, not
    `⟨w, by ring⟩`** (`k ∣ n^s*(b*(c*k))` is
    `dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_left k c) b) _`).
    Also `dvd_pow_self` needs its base given explicitly when the exponent is
    implicit: `dvd_pow_self (n : ℤ) hne`.
11. **`IsCoprime` toolkit on ℤ** (all used in L6): `Int.isCoprime_iff_gcd_eq_one`
    (`IsCoprime m n ↔ Int.gcd m n = 1`), `Int.isCoprime_iff_nat_coprime`
    (`↔ Nat.Coprime m.natAbs n.natAbs` — the cheap way to get
    `IsCoprime ((n:ℤ)^2) 2` from `Nat.Coprime (n^2) 2`),
    `IsCoprime.mul_dvd`, `.dvd_of_dvd_mul_left/right`, `.mul_left/mul_right`,
    `.pow_left/pow_right`, `.symm`. `Int.Prime.dvd_mul' hn` is the
    `n ∣ a*b → n ∣ a ∨ n ∣ b` splitter.
12. **A big `∃` binds its witnesses first.** `∃ a a' b b' : ℤ, …` needs
    `exact ⟨a, a', b, b', ha0, …⟩` — listing `a, a'` and then the `a`-part
    conjuncts costs a round ("argument ha0 has type a ≠ 0 but is expected to
    have type ℤ"). And a *conjunct* that is itself an `∃` must be destructed:
    `obtain ⟨⟨k₂, hk₂⟩, ⟨k₁, hk₁⟩⟩`.
13. **Cost/rhythm:** 13 rounds, 300–414 s each (one container, no
    contention): 1 batched `#check` probe, 6 single-step rounds, 5 batch
    rounds once green, 3 repair rounds (7 + 6 + 1 error sites). 35
    declarations (23 author steps + 12 helpers); `sorry`-free, only the three
    permitted axioms, zero warnings.

## Session 2026-09-26 — L7-FRAG-01 (bổ đề 7, non-divisibility) lane restart

State: `03-lean/L7/Basic.lean` compiles EXIT:0, zero warnings, zero `sorry`;
`#print axioms` on `L7_step_S0`, `L7_step_S1`, `L7_step_S2`,
`L7_step_S3_S4`, `L7_step_S5a`, `L7_step_S5b`, `L7_modEq_of_zmod_eq`,
`L7_tail_three`, `L7_pair_reductio` = propext / Classical.choice / Quot.sound
only. Nine rounds (1 bulk `#check` probe + 6 step rounds + 2 repair rounds) and
three one-shot tactic probes; per-round diagnosis in
`03-lean/L7-FRAG-01_compile_20260926.log`. The chunk stays BLOCKED on the open
author query Q-001 (its S6 is not encoded). All names pinned by the probe:
`pow_eq_zero_iff`, `dvd_pow_self`, `sub_eq_zero`, `neg_inj`,
`add_eq_zero_iff_eq_neg`, `mul_eq_zero`, `mul_eq_zero_iff_right`, `pow_ne_zero`,
`mul_pow`, `Odd.neg_pow`, `Nat.Prime.odd_of_ne_two`, `Nat.Prime.eq_two_or_odd'`,
`Int.Prime.dvd_pow'`, `Int.modEq_zero_iff_dvd`, `Int.modEq_iff_dvd`,
`Int.natCast_dvd_natCast`, `ZMod.intCast_zmod_eq_zero_iff_dvd`,
`ZMod.pow_card_sub_one_eq_one`, `ZMod.pow_card`,
`L5.L5_zmod_intCast_eq_zero_iff`, `L5.L5_gcd_eq_one_of_not_dvd`.

1. **`ZMod n` with a variable modulus is context-sensitive: the same tactic
   fails inside a longer proof and passes in a standalone `example`.** In the
   lane's first ZMod draft, `ring` failed on `-x + -x = -(x * 2)`
   (`⊢ -↑b ^ n + -↑b ^ n = -(↑b ^ n * 2)`), on `↑b ^ e + -↑b ^ e = 0`, and on
   numerals (`⊢ 3 + -3 = 0` for `-((4 : ZMod n) - 1) + 3 = 0`); `rw
   [Odd.neg_pow hodd2]` reported "did not find an occurrence of the pattern
   `(-?a) ^ (n - 2)`" in a goal printing exactly that. A controlled probe then
   showed the trigger is *instance scope*: with `[Fact (Nat.Prime n)]` as a
   theorem **binder** those goals fail, while the same code with the instance
   introduced **in-proof** (`have : Fact (Nat.Prime n) := ⟨hn⟩`, the L5
   pattern) closes in isolation. Also reproducible: `rw [neg_zero]` on
   `-0 + 3 = 0` ("did not find `-0`") — the L5 session's `- 0` note again.
   Consequence adopted here: **carry mod-`n` arguments in ℤ, not in `ZMod n`
   with a variable modulus** (item 2).
2. **The ℤ replacement (all verified at this pin):** `Int.ModEq` algebra —
   `h.pow k`, `h1.add h2`, `h1.mul h2`, `h.neg`, `h.add_left c`,
   `h.add_right c`, `h1.trans h2`, `h.symm`, `Int.ModEq.refl a` — plus
   `Int.modEq_iff_dvd` (`a ≡ b [ZMOD n] ↔ n ∣ b - a`; read `≡` as `n ∣ b - a`
   in whichever direction the algebra needs), `Int.modEq_zero_iff_dvd`,
   `dvd_neg`, `dvd_sub`, `dvd_add`, `dvd_mul_of_dvd_right`,
   `Int.natCast_dvd_natCast`, `Nat.le_of_dvd`,
   `ZMod.intCast_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ)`. Term-shape changes
   between ℤ facts are `by ring` / `by omega` — reliable in ℤ.
3. **`have hid : <numeral identity> = 3` DEFAULTS TO `ℕ`** when nothing pins the
   type — and in ℕ the identity is false (truncated subtraction), so `ring`
   fails on `2 * (2 - 2 ^ (n - 2)) + (2 ^ (n - 1) - 1) = 3` and the report looks
   like a broken `ring` rather than a wrong type. Write
   `have hid : (2 * (2 - 2 ^ (n - 2)) + (2 ^ (n - 1) - 1) : ℤ) = 3`. Rule: any
   pure-numeral `have` in a ℤ proof needs the `: ℤ` annotation.
4. **Bổ đề 5's FLT helper removes the `Fact` instance from ℤ proofs:**
   `Int.ModEq.pow_card_sub_one_eq_one (hn : Nat.Prime p) (hcop : IsCoprime n ↑p)`
   with `hcop` from `L5.L5_gcd_eq_one_of_not_dvd hn (h : ¬ (n : ℤ) ∣ u) :
   Int.gcd u (n : ℤ) = 1` via `Int.isCoprime_iff_gcd_eq_one.mpr`; then
   `h.symm.dvd : n ∣ 2 ^ (n - 1) - 1` reads the congruence as divisibility.
   (Alternative pinned route: `Nat.Prime.coprime_iff_not_dvd Nat.prime_two` +
   `Int.isCoprime_iff_nat_coprime`.)
5. **Cancelling a factor modulo a prime needs no field:** from `n ∣ A * b^e`
   and `¬ n ∣ b`, `Int.Prime.dvd_mul' hn` splits the product and
   `Int.Prime.dvd_pow' hn` refutes the second branch — the ℤ analogue of the
   author's "vì b ≢ 0".
6. **`pow_eq_zero` does not exist at this pin.** `pow_eq_zero_iff` needs
   `[IsReduced M₀]` and `n ≠ 0`, and `IsReduced (ZMod n)` requires
   `Fact (Squarefree n)` (`Mathlib/RingTheory/ZMod.lean:50`) — a prime modulus
   does not supply it, so `pow_ne_zero` is not directly available in `ZMod p`
   either. Prove nonzero powers from the field (`x ^ k * (x⁻¹) ^ k = 1` via
   `← mul_pow`, `mul_inv_cancel₀`, `one_pow`, `one_ne_zero`) or stay in ℤ.
7. **Oddness bridges that compiled:** `Nat.Prime.odd_of_ne_two (hn) (p ≠ 2) :
   Odd p` (note `Nat.Prime.eq_two_or_odd` returns `n % 2 = 1`, while
   `eq_two_or_odd'` returns `Odd p`), and `Odd (n - 2)` from `Odd n` via
   `obtain ⟨k, hk⟩ := hodd; exact ⟨k - 1, by omega⟩`.
8. Cost: 285–375 s per `import Mathlib` round; the three tactic probes
   (343–358 s) were the cheapest way to settle the `ZMod n` question before
   rewriting the lane in ℤ.

## Session 2026-09-27 — L7-FRAG-01 closed (S5c + S6, one round, zero F2)

The chunk's open F4 ("the printed product's first factor is the difference
`a^n − b^n`, which no printed step excludes") was **withdrawn**, not proved
around. Two findings, in this order:

1. **Check how the main proof USES the lemma before escalating to the author.**
   Grepping the signed region records (`01-extract/regions/p*.yml`) for the
   lemma's name outside its own pages found exactly two citations: p30 R2 (the
   congruence conclusions) and p32 R1, where the case `h = c^n` closes by
   cancelling `a^n b^n (a^n − b^n)(a^n + b^n) ≢ 0 (mod n)` out of a product
   `≡ 0 (mod n^{s+1})`. Only one of those four factors is non-trivial
   (`a^n, b^n` from `abc ∤ n`; `a^n + b^n` from the case hypothesis) — the
   **difference**, i.e. the statement's sign as printed. That single data point
   turned "one of the two printed signs is a typo" into "the statement is
   right; the printed proof's enumeration is incomplete".
2. **The missing instance was the printed chain re-instantiated.** The print's
   own "Lưu ý" symmetry (`(a; b)`, `(c; −a)`, `(c; −b)`) makes the existing
   abstractions consume (b)/(c) verbatim at `(X, Y, Z) = (−b, a, c)`, whose
   conclusion is `¬n ∣ a^n − b^n`. Both new declarations compiled on the first
   attempt (EXIT 0, zero warnings, 148 s round).

Reusable API/technique facts confirmed here:

- `Odd.mul : Odd a → Odd b → Odd (a * b)` (so `Odd (n * (n - 2))` from
  `Odd n` + `Odd (n - 2)`), and `Odd.neg_pow (h : Odd k) (a) : (-a) ^ k = -a ^ k`
  — one rewrite gives `(−b)^{n(n−2)} = −b^{n(n−2)}`, no case analysis on the
  exponent's parity.
- `dvd_neg : a ∣ -b ↔ a ∣ b` (and `neg_dvd`) are the whole bridge for passing
  `¬ n ∣ b` to the instantiated chain's `X = -b`.
- `Int.Prime.dvd_mul' (hp : Nat.Prime p) (h : (p : ℤ) ∣ m * n) : (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n`
  — the print's "Tóm lại" (a prime dividing a product divides a factor);
  `Int.Prime.dvd_pow'` is its power form, used for cancellation.
- Rearranging a printed congruence for an instantiation is cheapest as a
  divisibility obligation plus `ring`, e.g. for `a^n ≡ c^n + (−b)^n`:
  `refine (Int.modEq_iff_dvd).mpr ?_` / `have hid : (c ^ n + (-b) ^ n) - a ^ n = -((a ^ n + b ^ n) - c ^ n) := by rw [hnb]; ring` /
  `rw [hid]; exact dvd_neg.mpr hd`. No `Int.ModEq` combinator chain needed.
- **F3 vs F4 is decided by downstream use plus derivability from the author's
  own material, not by "the printed page has no such step".** The classification
  moved to F3 once (i) the main proof required the instance and (ii) the print's
  own symmetry instantiation produced it. Recorded in the chunk YAML, and Q-001
  turned from an author blocker into an editorial note (the printed "tương tự"
  line could name the difference instance).


## Session 2026-09-28 — L7-FRAG-02 … L7-FRAG-06 + L7-ASM (bổ đề 7 done, all S1)

26 declarations over six chunks (L7-FRAG-02 … L7-FRAG-06 + the assembly
L7-ASM) in about 28 container rounds — but only ~10 of those rounds carried
real errors, and **every one was F2** (encoding/API; no F1/F4 anywhere in the
lane). The rest were cascade failures (a leaf's olean missing after an earlier
failed round in the same chain) or clean. What cost the rounds, and the exact
names/signatures — checked against the pinned tree, not guessed:

1. **`Int.gcd_comm` does not exist.** The generic `gcd_comm` is *not*
   `Int`-namespaced, so `rw [Int.gcd_comm]` fails. To get
   `IsCoprime (↑n) X` from the ℤ-gcd helper:
   `Int.isCoprime_iff_gcd_eq_one.mpr` needs `Int.gcd X ↑n = 1` — the order
   `L5_gcd_eq_one_of_not_dvd hn hX` returns — so derive `IsCoprime X ↑n` and
   flip with `IsCoprime.symm`.

2. **`IsCoprime.pow` / `pow_left` / `pow_right` take their exponents
   implicitly** (`{m n : ℕ}`); `h.pow 2 1` is a hard error ("expected a
   function"). Use named arguments: `h.pow_left (m := 2)`,
   `h.pow (m := 2) (n := 1)`. Also: unification cannot invent an exponent when
   the goal's term is not syntactically a power (`X` vs `X ^ 1`), so prefer
   `pow_left` (which keeps the second factor as-is) over `pow` + `simpa`.

3. **`(n ^ 2 : ℤ)` *is* `(↑n) ^ 2`.** The ascription forces the power into ℤ,
   so no `Nat.cast_pow` bridge is needed — and `rw [Nat.cast_pow]` on
   `↑n ∣ ↑n ^ 2` fails with "did not find an occurrence". The same fact makes
   `Int.ModEq.of_dvd (dvd_pow_self (n : ℤ) (by norm_num)) h` the one-liner that
   lowers `[ZMOD (↑n)^2]` to `[ZMOD ↑n]` (`dvd_pow_self`'s hypothesis is about
   the *exponent* being nonzero).

4. **Prefix `-` binds tighter than `^`** (again): `-(c ^ n) ^ k` is
   `((-(c^n))^k)`, not `-((c^n)^k)`. Inside `ring`, the former becomes
   `c^(n*k) * (-1)^k` and then ring stalls on `(-1)^k = -1`. Write
   `-((c ^ n) ^ k)` and, for odd `k`, rewrite with
   `Odd.neg_pow (hodd : Odd k) (c ^ n) : (-(c^n))^k = -((c^n)^k)`.

5. **`pow_add` produces `x ^ (m + n)` from `x ^ m * x ^ n`.** State the ℕ
   exponent identity in that order; for a product written the other way round,
   add a mirrored copy via `Nat.add_comm` (four lines, `Nat.mul_add` +
   `Nat.sub_one_add_one_eq_of_pos`). Two traps: `omega` cannot do these
   (nonlinear `n * (n - 2)`), and `Nat.sub_one_add_one_eq_of_pos` needs the
   literal `(n - 1) + 1`, not `n.succ - 1` / `Nat.succ (n-1)`.

6. **`omega` cannot read `Nat.Prime n`.** Any omega that needs `2 ≤ n` must be
   given `have h2 : 2 ≤ n := hn.two_le` first. (It *can* close
   `n % 6 = 1 ∨ n % 6 = 5` from `n % 2 = 1` + `n % 3 ≠ 0`, and the
   `% 3` / `% 2` residue facts of S16/S17.)

7. **`Nat.dvd_prime` goes the divisor way** (`m ∣ p ↔ m = 1 ∨ m = p`). For
   `3 ∣ n` with `n` prime, use
   `Nat.Prime.dvd_iff_eq (hn) (a1 : a ≠ 1) : a ∣ p ↔ p = a` (or
   `Nat.Prime.dvd_prime_iff_eq`).

8. **`rwa [h] at X` = `rw` + `assumption`.** When `X` is a divisibility and the
   goal is a `≡`, the trailing `assumption` fails; use
   `rw [h] at X` then `exact Int.modEq_zero_iff_dvd.mpr X`. Likewise mind
   directions: `Int.modEq_zero_iff_dvd.mp : a ≡ 0 → n ∣ a`,
   `.mpr : n ∣ a → a ≡ 0`; `Int.modEq_iff_dvd` is about `n ∣ b - a`, so
   `h.mpr` wants the *reversed* difference.

9. **`dvd_add` needs both summands of the same term shape.** To assemble
   `n² ∣ big` from `n² ∣ small` and `n² ∣ big - small`, do
   `dvd_add hsmall hdiff` and then rewrite with an explicit `ring` identity —
   `dvd_add hdiff hsmall` elaborates against the wrong side.

10. **Modulus discipline per step.** Take an author step's inputs at the
    modulus the *source line* uses, not at the strongest available one: the
    printed (c) is mod `n` while (b) is mod `n²`, and feeding S3 the mod-`n²`
    form is a type error the assembly surfaces only at the end.

11. **Compile-cost note (this machine, this session):** one warm
    `import Mathlib` round is **~250–340 s**, and the harness backgrounds long
    commands, so chain several files in ONE container call
    (`sh compile_lean.sh A; sh compile_lean.sh B`) and read the per-file logs
    afterwards; the per-round cost is dominated by re-loading Mathlib, not by
    the declarations.

## Session 2026-09-28 — M1 lane (main proof §D.1, pp. 6–33): M1-FRAG-01 DONE

Each item below cost one round to learn; all are cheap to avoid now.

1. **Big-operator binder: write `∑ i ∈ s,`. The ASCII `∑ i in s,` form does not
   parse at this pin.** `B/Basic.lean` round 5 died with
   `B/Basic.lean:49:8: error: unexpected token 'in'; expected ','` on
   `(∑ i in Finset.Ico k (n + 1), a i)`. `L5/Basic.lean` and `L6/Basic.lean`
   (both DONE) use `∑ i ∈ Finset.range n,` with nothing but `import Mathlib` —
   there is no `open scoped BigOperators` anywhere in this repo. Cost: one round.
2. **`Finset.sum_Icc_eq_sum_range` does NOT exist.** `rg` the pinned tree under
   `/workspace/work/testproj/.lake/packages/mathlib/Mathlib` *before* writing a
   proof (≈1 s versus a 250–400 s round). What exists and is useful:
   `Finset.sum_Ico_eq_sum_range` and `Finset.sum_range_reflect`. The printed
   `Σ_{i=k}^{n}` translates with no side condition as `Finset.Ico k (n + 1)`,
   and the printed `Σ_{i=k}^{m-1}` is exactly `Finset.Ico k m`.
3. **`async: true` does not extend the harness's command deadline.** A round
   launched with the default deadline was killed at 300 s mid-compile (it needed
   ~320 s): the log file came back 0 bytes and no ledger row was written, and the
   side effect was a stale `M1_inflight` handshake to clear. Always pass an
   explicit generous `timeout` (≥ 1200 s) to a `sh proof/run_round.sh` call.
4. **`Nat.Prime.prime_int` does not exist** (caught by a probe line, round 3).
   The nat→ℤ prime bridge that works is
   `Int.prime_iff_natAbs_prime.mpr (by simpa using hn)`, then
   `hprime.dvd_mul.mp` for the `p ∣ a * b` split.
5. **`Odd.neg_pow : Odd n → ∀ a, (-a) ^ n = -a ^ n`.** A four-way sign symmetry
   over ℤ needs nothing else: `rw [hodd.neg_pow, hodd.neg_pow]` then `linarith`.
   `Nat.Prime.odd_of_ne_two` (with `omega` on a numeric lower bound) supplies the
   `Odd n`; `Nat.Prime.two_le` is what `omega` needs otherwise, since it cannot
   read `Nat.Prime` itself.
6. **Batching the probe with the first proof attempt works.** Put the `#check`
   pin block at the top of the *same* file as the step. Round 3 returned exactly
   one error — a bad probe name — and zero proof errors for four declarations, so
   the single re-round was only to delete the name. This is the cheap version of
   "probe in bulk, then one step per compile".
7. **`#print axioms` costs nothing inside the same round.** Append
   `#print axioms <decl>` lines after `end <Namespace>`; the round log then
   carries the DONE-flip evidence directly (`propext, Classical.choice,
   Quot.sound` only).
8. **New modules need a `[[lean_lib]]` block in `pipeline/03-lean/lakefile.toml`**
   (`roots = ["M1F1.Basic"]`) or a consumer's `import M1F1.Basic` will not
   resolve; `proof/compile_lean.sh` syncs that tracked file into the work volume.
   `gen_signatures.py`'s `MODULES` list must also name the module, and its
   *body* and *imports* both skip a module whose `Basic.lean` does not exist yet
   (the import list originally did not — an unconditional `import B.Basic` for an
   unwritten module makes the whole 119-line probe fail to elaborate).

## General advice

1. **Don't fight ZMod.** If the proof needs heavy algebra in `ZMod n`,
   consider whether the same steps can be done in `ℤ` with divisibility.
   `linarith`/`omega` work natively on `ℤ`.

2. **`ring` and `field_simp` work in ZMod.** Use them for algebraic
   simplification. `linarith`/`omega` do not.

3. **Test with specific n first.** If something doesn't compile for
   variable `n`, try `n = 7` or `n = 11` to distinguish API issues from
   logic errors.

4. **One `lake env lean` per author step.** Compile immediately after
   encoding *one* step and classify it (AGENTS.md one-step loop); never
   batch several author steps into one compile — a cascade of errors costs
   a full round-trip to untangle (`L7-FRAG-01` compile #1 is the evidence).
   Batch only *name probes* (`#check`) into one file. Measured cost at this
   pin: **~5–6.5 min** per warm `import Mathlib` compile under load
   (288–387 s across this session), so a wrong guess is expensive: grep the
   local Mathlib tree first (free, pin-exact) and spend the round-trip on
   the step itself.

5. **Correction to item 4's cost model, measured 2026-09-28 (pp. 9–10 lane).**
   A round that *fails* costs **7–24 s**, not 250–400 s: Mathlib's oleans are
   cached in the work volume, so `import Mathlib` is cheap and the multi-minute
   rounds are the ones where heavy tactics (`ring`, `omega`) elaborate
   successfully over large terms. Consequences, both used to good effect:
   (a) iterate freely on compile errors inside one session — a wrong guess is
   8 s, not 6 min; (b) the round-trip is only expensive when the goal is big, so
   keep each round to one author step (item 4) and do not pre-emptively fear the
   compile. Measured on `B/Basic.lean`: rounds 17 and 18 failed in 24 s and 8 s,
   round 19 (a 13-name `#check` probe) in 7 s, and rounds 20 and 21 — one
   accepting the proof, one printing the axiom sets — in 8 s each, EXIT 0.

6. **`omega` and truncated subtraction, the second failure of this kind.**
   `omega` CAN do equalities of truncated chains
   (`m - 1 - k - i = m - 1 - i - k` ✓, used in `B_step_S2_deriv` and in
   `B_step_S1_reindex`'s `e1/e2/e3`) and the *easy* comparison
   (`y < m - k ⊢ y < m` ✓). It CANNOT do monotonicity in the subtrahend:
   `y ≥ m - k ⊢ m - 1 - y < k` fails, and the counterexample it prints reveals
   why — it abstracts `↑(m - k)` as an atom, so the two facts are unrelated in
   its model. Working recipe (2 lines of core lemmas + one `omega`):
   ```lean
   have hyk : m ≤ y + k := by
     calc m = m - k + k := (tsub_add_cancel_of_le hk_le).symm
       _ ≤ y + k := Nat.add_le_add_right hyge k
   rw [Nat.sub_sub, Nat.add_comm 1 y, tsub_lt_iff_right hy1]   -- hy1 : y + 1 ≤ m
   omega                                                        -- now purely linear
   ```
   The same weakness forced B.1's range-form encoding (see `B-01.yml`), so the
   general rule is: **when a goal compares two different truncated subtractions,
   convert to an addition (`tsub_lt_iff_right`, `Nat.sub_sub`) before calling
   `omega`.**

7. **`Finset.sum_subset` exists but is invisible to `rg`, and its set order is
   the opposite of the natural reading.** It is the `to_additive` image of
   `Finset.prod_subset`, generated at elaboration time, so
   `rg "theorem sum_subset"` over the pinned tree finds nothing — do not
   conclude the lemma is absent. Probe statement (round 19):
   ```lean
   Finset.sum_subset : s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑ x ∈ s₁, f x = ∑ x ∈ s₂, f x
   ```
   The **smaller** set is on the LEFT and the vanishing condition is stated on
   the *bigger* set's elements. So a goal written
   `∑ over range m = ∑ over range (m-k)` needs `(Finset.sum_subset h hf).symm`;
   without the `.symm` Lean still elaborates it (unifying `s₁ := range m`), and
   the two subgoals come back swapped, which reads as an arithmetic error rather
   than a direction error. Two rounds were spent on this.

8. **One `#check`/`#print` probe round pins a dozen shapes at once, for 7 s.**
   Round 19 resolved 12 of 13 names in a single round (`Finset.sum_range_eq_add_sum_Ico`
   is the one that does not exist). Pinned there and reused immediately:
   `tsub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b`;
   `tsub_add_cancel_of_le (h : a ≤ b) : b - a + a = b` (the ℕ-generic spellings —
   note these are the *unbundled* names, not `Nat.sub_lt_iff_lt_add`, which does
   not exist under that name); `Nat.sub_sub n m k : n - m - k = n - (m + k)`;
   `Nat.succ_le_iff : m.succ ≤ n ↔ m < n`; `Nat.sub_le n m : n - m ≤ n`;
   `Nat.le_of_not_lt : ¬a < b → b ≤ a`; `Finset.sum_range_add`,
   `Finset.sum_union`, `Finset.sum_eq_zero`.

9. **A text edit that swallows a `·` bullet marker silently merges two goals** —
   the failure mode to recognise, because its two symptoms point opposite ways.
   Rewriting the first line of a bullet (`  · rw [...]`) with replacement text
   that starts at the tactic (`    rw [...]`) loses the `·`; the following lines
   then belong to the *previous* bullet, which had already closed — so Lean
   reports **`No goals to be solved`** at the merged tactic *and* **`unsolved
   goals`** at the `refine`/`constructor` site that introduced the real second
   goal. Reading only the first symptom looks like a type error; reading only
   the second looks like a missing proof. It is neither. Cost: rounds 25 and 26
   on `M1-FRAG-03` (12 s and 10 s, one error each, no mathematics involved).
   Prevention: when a replacement's `old_string` begins mid-line, keep the line's
   leading marker (`·`, `case …`), or anchor the edit one line earlier.

10. **`rw` closes a goal that becomes `rfl`.** After
   `rw [h, Finset.sum_range_add]` over the split of a sum, the goal is
   `∑ … + ∑ … = ∑ … + ∑ …` with syntactically identical sides, and the `rw`
   already finishes it — so a follow-up `simp only [add_left_inj]; rfl` errors
   with `No goals to be solved` (`M1-FRAG-03`, round 26). When a `rw` chain is
   expected to leave only bookkeeping, try ending at the last `rw` first; the
   binding lemma here was `Finset.sum_range_add` plus the range equality
   `n + 1 = (r + 1) + (n - r)`.

11. **A printed exponent split that is valid over ℤ can be FALSE when the
   exponent is encoded in ℕ — check the boundary index.** This one is an F1
   waiting to happen, and it produced the lane's first F1 (`M1-FRAG-04`,
   round 31, 9 s). The author writes the same sum two ways:

   `R2: Σ_{i=0}^{n} C(n,i) a^{(n-1)(n-i)} (n^s bck)^i`
   `R3: Σ_{i=0}^{n} C(n,i) a^{n(n-1-i)} (n^s abck)^i`

   They are equal, because `n(n-1-i) = (n-1)(n-i) - i` — at `i = n` R3's
   exponent is `-n`, which cancels the bracket's `a^n`. **But in ℕ, `n - 1 - i`
   at `i = n` truncates to `0`, so the R3 form is off by a factor `a^n` and the
   split identity `a^{n(n-1-i)} (n^s abck)^i = (a^{n-1})^{n-i} (n^s bck)^i` is
   simply false there.** `omega` refusing the arithmetic was the compiler telling
   us the statement was wrong, not that the proof was hard. Rules that follow:
   * encode the form whose exponents are ℕ-safe (here R2, which is also the
     `add_pow` form), and *say so* in the docstring;
   * if a lemma needs the split, restrict it to the low-order indices where the
     subtraction is exact (`i + 1 ≤ n`) — `M1F4_absorb` carries exactly that;
   * before believing a "different" printed form, check whether the difference is
     confined to the final index (run it: the difference was 0 for every `i ≤ n-1`
     and `a^n` at `i = n`).

12. **`rw [pow_mul]` can hit the wrong side.** In
   `a ^ (n * (n - 1 - i)) * X = (a ^ (n - 1)) ^ (n - i) * Y` both sides match the
   lemma's pattern `a ^ (m * n)`, and `rw` takes the first occurrence — the left
   one. Use an explicit equation for the side you mean
   (`rw [show … from (pow_mul a (n-1) (n-i)).symm]`), or `nth_rewrite`
   (`M1-FRAG-04`, round 33). The same applies to `mul_pow` when both sides carry
   a bracket power.
