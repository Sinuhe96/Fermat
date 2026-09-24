# Mathlib API Lessons Learned

Hard-won knowledge for encoding elementary number theory proofs in Lean 4
+ Mathlib v4.35.0-rc2. Every item here cost real compilation time.

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

## General advice

1. **Don't fight ZMod.** If the proof needs heavy algebra in `ZMod n`,
   consider whether the same steps can be done in `ℤ` with divisibility.
   `linarith`/`omega` work natively on `ℤ`.

2. **`ring` and `field_simp` work in ZMod.** Use them for algebraic
   simplification. `linarith`/`omega` do not.

3. **Test with specific n first.** If something doesn't compile for
   variable `n`, try `n = 7` or `n = 11` to distinguish API issues from
   logic errors.

4. **One `lake env lean` per session.** The compilation is slow (~30s for
   a file with `import Mathlib`). Batch your changes and compile once.
