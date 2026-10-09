import Mathlib

/-!
# CJ probe — conjecture lane (Phase 4), Block 1/2 API pinning

Lane: side-lane formalization of the n=6l+1 valuation conjecture
(see HANDOFF_CONJECTURE.md). NOT part of the PDF FLT pipeline.

Header: 2026-09-30, toolchain lean 4.35.0-rc2, Mathlib v4.35.0-rc2
rev 06535612…, command:
  sh /workspace/proof/compile_lean.sh CJ/PROBE.lean
Log: pipeline/03-lean/CJ_probe.log
Status: UNVERIFIED until log shows EXIT=0
-/

-- Polynomial division / modByMonic (grep-confirmed Algebra/Polynomial/Div.lean)
#check @Polynomial.modByMonic_add_div
#check @Polynomial.modByMonic_eq_zero_iff_dvd
#check @Polynomial.modByMonic_eq_zero_iff_quotient_eq_zero
#check @Polynomial.natDegree_modByMonic_lt
-- #check @Polynomial.modByMonic_eq_of_degree_lt  -- absent at this pin

-- roots / divisibility bridges
#check @Polynomial.dvd_iff_isRoot
-- #check @Polynomial.exists_eq_mul_right_of_dvd  -- root version below works
#check @exists_eq_mul_right_of_dvd
#check @Polynomial.C_dvd_iff_dvd_coeff
#check @Polynomial.coeff_C_mul
#check @Polynomial.coeff_X_add_C_pow
#check @Polynomial.coeff_X_pow
#check @Polynomial.eval_pow
#check @Polynomial.eval_sub
#check @Polynomial.eval_neg
#check @Polynomial.eval_X
#check @Polynomial.eval_one

-- degrees & maps
#check @Polynomial.natDegree_mul
#check @Polynomial.natDegree_X_add_C
#check @Polynomial.natDegree_map
#check @Polynomial.map_eq_zero

-- derivatives
#check @Polynomial.derivative_pow
#check @Polynomial.derivative_X_add_C
#check @Polynomial.derivative_mul
#check @Polynomial.derivative_sub
#check @Polynomial.derivative_X
#check @Polynomial.derivative_C
#check @Polynomial.derivative_X_pow

-- quotient ring Z[X]/(X^2+X+1)
#check @Ideal.Quotient.mk
-- #check @Ideal.Quotient.mk_self  -- absent at this pin
-- #check @Ideal.Quotient.mk_eq_zero  -- absent at this pin
#check @Ideal.Quotient.eq_zero_iff_dvd
#check @Ideal.mem_span_singleton
#check @eq_neg_of_add_eq_zero_left

-- coprime combination
#check @IsCoprime.mul_dvd
#check @IsCoprime.dvd_of_dvd_mul_left
#check @IsCoprime.symm

-- irreducible -> prime (Q[X])
#check @Polynomial.irreducible_of_degree_le_three_of_not_isRoot
#check @Irreducible.prime
#check @Prime.dvd_or_dvd
#check @Prime.ne_zero
#check @Polynomial.IsRoot.def

-- binomial & parity
-- #check @Nat.dvd_choose_add  -- absent; `hn.dvd_choose_self` is the working name
-- #check @dvd_choose_add  -- absent at this pin
#check @Even.neg_one_pow
#check @Odd.neg_pow

-- Block 2 valuation
#check @padicValNat_dvd_iff_le
-- #check @Nat.padicValNat_dvd_iff_le  -- absent; unqualified name works
#check @padicValNat.mul
-- #check @Nat.padicValNat.mul  -- absent; unqualified name works
#check @padicValNat.eq_zero_of_not_dvd

-- ===== 2026-09-30: CJ_valuation round blockers =====
-- (a) extracting Nat.Prime n from the [Fact (Nat.Prime n)] binder
#check @Fact.out

-- P1 removed: positional `Fact.out h` always fails (lesson 28; failure in CJ_probe.log).

example (n : ℕ) [Fact (Nat.Prime n)] : Nat.Prime n :=
  (‹Fact (Nat.Prime n)›).out   -- P2: dot-notation on the notation

-- P3 removed: same positional `Fact.out` failure as P1 (lesson 28; failure in CJ_probe.log).

example (n : ℕ) [Fact (Nat.Prime n)] : Nat.Prime n :=
  (by assumption : Fact (Nat.Prime n)).out   -- P4

example (n : ℕ) [Fact (Nat.Prime n)] : Nat.Prime n := by
  obtain ⟨p⟩ := ‹Fact (Nat.Prime n)›
  exact p   -- P5

example (n : ℕ) [Fact (Nat.Prime n)] : Nat.Prime n :=
  (inferInstance : Fact (Nat.Prime n)).out   -- P6

-- (b) the standalone pow split, calc step shape
-- Q1 removed: `rw [padicValNat.pow …]` never matches its own LHS (lesson 29; failure in CJ_probe.log).

example (n : ℕ) [Fact (Nat.Prime n)] (x : ℤ) (X : ℕ) :
    padicValNat n (n * x.natAbs * (x + 1).natAbs)
        + padicValNat n ((x ^ 2 + x + 1).natAbs ^ 2) + X =
    padicValNat n (n * x.natAbs * (x + 1).natAbs)
        + 2 * padicValNat n (x ^ 2 + x + 1).natAbs + X := by
  have hpow : padicValNat n ((x ^ 2 + x + 1).natAbs ^ 2) =
      2 * padicValNat n (x ^ 2 + x + 1).natAbs := padicValNat.pow _ 2
  rw [hpow]   -- Q2: have + concrete-pattern rewrite

example (n : ℕ) [Fact (Nat.Prime n)] (x : ℤ) (X : ℕ) :
    padicValNat n (n * x.natAbs * (x + 1).natAbs)
        + padicValNat n ((x ^ 2 + x + 1).natAbs ^ 2) + X =
    padicValNat n (n * x.natAbs * (x + 1).natAbs)
        + 2 * padicValNat n (x ^ 2 + x + 1).natAbs + X := by
  simp only [padicValNat.pow]   -- Q3

-- Q4 removed: same failure even fully explicit (lesson 29; failure in CJ_probe.log).
