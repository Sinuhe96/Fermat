import Mathlib

/-!
# Block 1 — factorization identity for `F n = (X+1)^n - X^n - 1`

Side-lane formalization for the n=6l+1 valuation conjecture
(see `HANDOFF_CONJECTURE.md`). NOT part of the PDF FLT pipeline.

Target (prime `n = 6*l+1`): `F n = C n * X * (X + C 1) * (X^2+X+1)^2 * E`.

Status: all Block-1 lemmas sorry-free (R17); `D_dvd_of_deriv_rel`'s
route notes live in its docstring.
-/

namespace CJ

open Polynomial

-- ===== mini-probe: names used below; errors surface in this same round =====
#check (inferInstance : DecompositionMonoid (Polynomial ℚ))
#check (inferInstance : UniqueFactorizationMonoid (Polynomial ℤ))
#check @Polynomial.coeff_sub
#check @sub_eq_add_neg
#check @neg_neg
#check @Nat.choose_zero_right
#check @eval_dvd
#check @Nat.choose_eq_zero_of_lt

/-- `F n (X) = (X+1)^n - X^n - 1` over `ℤ`. -/
noncomputable def F (n : ℕ) : ℤ[X] := (X + C 1) ^ n - X ^ n - C 1

private abbrev CQ : Type := ℤ[X] ⧸ (Ideal.span {X ^ 2 + X + 1} : Ideal ℤ[X])

private noncomputable def mkQ : ℤ[X] →+* CQ :=
  Ideal.Quotient.mk (Ideal.span {X ^ 2 + X + 1} : Ideal ℤ[X])

/-! ### Quotient facts: mod `X^2+X+1` we have `X^6 = 1` and `(X+1)^6 = 1` -/

private lemma mkQ_D_zero : mkQ (X ^ 2 + X + 1) = 0 :=
  (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr (dvd_refl _)

private lemma mkQ_X6 : mkQ (X ^ 6) = 1 := by
  have hdvd : (X ^ 2 + X + 1 : ℤ[X]) ∣ X ^ 6 - 1 :=
    ⟨(X - 1) * (X + 1) * (X ^ 2 - X + 1), by ring⟩
  have h0 := (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr hdvd
  simp only [map_sub, map_one] at h0
  exact eq_of_sub_eq_zero h0

private lemma mkQ_Y6 : mkQ ((X + C 1) ^ 6) = 1 := by
  have heq : (X + C 1 : ℤ[X]) = X + 1 := by rw [show (1 : ℤ[X]) = C 1 from rfl]
  have hdvd : (X ^ 2 + X + 1 : ℤ[X]) ∣ (X + C 1) ^ 6 - 1 := by
    rw [heq]
    exact ⟨-2 * (X + 2) + (X ^ 2 + X + 1) * (X + 2) ^ 2, by ring⟩
  have h0 := (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr hdvd
  simp only [map_sub, map_one] at h0
  exact eq_of_sub_eq_zero h0

private lemma mkQ_Y6' : mkQ (X + C 1) ^ 6 = 1 := by
  rw [← map_pow]
  exact mkQ_Y6

private lemma mkQ_X6' : mkQ X ^ 6 = 1 := by
  rw [← map_pow]
  exact mkQ_X6

/-! ### Step A: `D ∣ F n` for `n = 6l+1` (no primality needed) -/

private lemma quotient_F (l : ℕ) : mkQ (F (6 * l + 1)) = 0 := by
  induction l with
  | zero =>
    simp only [F, Nat.mul_zero, Nat.zero_add, pow_one, map_sub, map_add]
    ring
  | succ l ih =>
    simp only [F] at ih ⊢
    have hexp : 6 * (l + 1) + 1 = (6 * l + 1) + 6 := by ring
    rw [hexp]
    rw [pow_add (X + C 1) (6 * l + 1) 6, pow_add X (6 * l + 1) 6]
    simp only [map_sub, map_mul, map_one]
    simp only [show (X + 1 : ℤ[X]) = X + C 1 from rfl]
    rw [mkQ_Y6, mkQ_X6, mul_one, mul_one]
    simp only [map_sub, map_one] at ih
    exact ih

/-- Step A: `X^2+X+1` divides `F n` for every `n = 6l+1`. -/
lemma D_dvd_F {n : ℕ} (hn6 : ∃ l, n = 6 * l + 1) : X ^ 2 + X + 1 ∣ F n := by
  obtain ⟨l, rfl⟩ := hn6
  exact (Ideal.Quotient.eq_zero_iff_dvd _ _).mp (quotient_F l)

/-! ### The linear factors -/

/-- `X` divides `F n` (root at 0; `n ≠ 0`). -/
lemma X_dvd_F (n : ℕ) (hn0 : 0 < n) : X ∣ F n := by
  have hroot : IsRoot (F n) 0 := by
    simp only [IsRoot.def, F, eval_sub, eval_add, eval_pow, eval_X, eval_C]
    rw [zero_pow (ne_of_gt hn0), zero_add, one_pow, sub_zero, sub_self]
  simpa [C_0] using (dvd_iff_isRoot.mpr hroot)

/-- `X+1` divides `F n` (root at -1; `n` odd). -/
lemma X1_dvd_F {n : ℕ} (hn6 : ∃ l, n = 6 * l + 1) : X + C 1 ∣ F n := by
  obtain ⟨l, rfl⟩ := hn6
  have hodd : Odd (6 * l + 1) := ⟨3 * l, by ring⟩
  have hroot : IsRoot (F (6 * l + 1)) (-1) := by
    simp only [IsRoot.def, F, eval_sub, eval_add, eval_pow, eval_X, eval_C]
    have hz : (-1 + 1 : ℤ) ^ (6 * l + 1) = 0 := by
      rw [neg_add_cancel, zero_pow (by omega)]
    have hm : (-1 : ℤ) ^ (6 * l + 1) = -1 := by
      rw [Odd.neg_pow hodd, one_pow]
    rw [hz, hm]
    norm_num
  have h := dvd_iff_isRoot.mpr hroot
  convert h using 1
  rw [C_neg, sub_eq_add_neg, neg_neg]

/-! ### The constant factor `n`: coefficients of `F n` are binomials -/

/-- `n` divides every coefficient of `F n` (prime `n`). -/
lemma n_dvd_F {n : ℕ} (hn : Nat.Prime n) : C (n : ℤ) ∣ F n := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro k
  by_cases hk : k = n
  · subst hk
    simp only [F, coeff_sub, coeff_X_add_C_pow, coeff_X_pow, coeff_C, Nat.choose_self,
      Nat.sub_self, pow_zero, Nat.cast_one, mul_one, sub_self, if_true, if_false,
      hn.ne_zero, dvd_zero]
  · by_cases hk0 : k = 0
    · subst hk0
      simp only [F, coeff_sub, coeff_X_add_C_pow, coeff_X_pow, coeff_C,
        Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one, sub_zero, sub_self,
        if_true, if_false, hk, dvd_zero]
    · by_cases hlt : k < n
      · simp only [F, coeff_sub, coeff_X_add_C_pow, coeff_X_pow, coeff_C, hk, hk0,
          Nat.cast_one, one_pow, one_mul, mul_one, sub_zero, if_true, if_false]
        exact_mod_cast hn.dvd_choose_self hk0 hlt
      · have hgt : n < k := by omega
        have hk0' : k ≠ 0 := fun h => by omega
        simp only [F, coeff_sub, coeff_X_add_C_pow, coeff_X_pow, coeff_C,
          Nat.choose_eq_zero_of_lt hgt, Nat.cast_zero, Nat.cast_one, mul_zero,
          sub_self, if_true, if_false, hk, hk0', dvd_zero]

/-! ### Step B part 1: `mk (F') = 0` in the quotient -/

private lemma quotient_deriv {n : ℕ} (hn6 : ∃ l, n = 6 * l + 1) :
    mkQ (derivative (F n)) = 0 := by
  obtain ⟨l, rfl⟩ := hn6
  simp only [F]
  rw [derivative_sub, derivative_sub, derivative_pow, derivative_pow,
    derivative_X_add_C, derivative_X, derivative_C, mul_one, mul_one]
  simp only [show (6 * l + 1) - 1 = 6 * l from by omega, sub_zero, map_sub, map_mul,
    map_pow, pow_mul, mkQ_Y6', mkQ_X6', mkQ_Y6, mkQ_X6, one_pow, mul_one, sub_self]

/-! ### Step B part 2: the key integer relation `(2X+1) * G = D * K` -/

private lemma deriv_relation {n : ℕ} {G : ℤ[X]} (hn6 : ∃ l, n = 6 * l + 1)
    (hFG : F n = (X ^ 2 + X + 1) * G) :
    ∃ K, (2 * X + 1) * G = (X ^ 2 + X + 1) * K := by
  have hq := quotient_deriv hn6
  rw [hFG] at hq
  simp only [derivative_mul, map_add, map_mul] at hq
  simp only [← map_add, ← derivative_add] at hq
  have hD' : derivative (X ^ 2 + X + 1 : ℤ[X]) = 2 * X + 1 := by
    simp only [derivative_add, derivative_X_pow, derivative_X, pow_one, C_eq_natCast]
    rw [show (derivative (1 : ℤ[X])) = 0 from (derivative_eq_zero).mpr natDegree_one]
    ring
  rw [hD', mkQ_D_zero, zero_mul, add_zero, ← map_mul] at hq
  exact exists_eq_mul_right_of_dvd ((Ideal.Quotient.eq_zero_iff_dvd _ _).mp hq)

/-! ### Step B part 3 (the hard bridge): cancel `(2X+1)` via `ℚ[X]` -/

private noncomputable abbrev φ (p : ℤ[X]) : ℚ[X] := Polynomial.map (Int.castRingHom ℚ) p
private noncomputable abbrev Dq : ℚ[X] := X ^ 2 + X + 1

-- ===== names for the ℚ[X] cancellation bridge (pinned: CJ_r14.log) =====
#check @Polynomial.natDegree_map_eq_of_injective
#check @Polynomial.map_eq_zero_iff
#check @Polynomial.map_add
#check @Polynomial.map_mul
#check @dvd_sub
example : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
example : (2 : ℤ[X]) = C (2 : ℤ) := (C_eq_natCast 2).symm
example : Monic (X ^ 2 + X + 1 : ℤ[X]) := by
  rw [show (X ^ 2 + X + 1 : ℤ[X]) = X ^ 2 + (X + 1) from by ring]
  exact monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_le_natDegree
    (by simp [natDegree_add_one]))
example : natDegree (2 * X + 1 : ℤ[X]) = 1 := by
  rw [natDegree_add_one, show (2 : ℤ[X]) = C 2 from (C_eq_natCast 2).symm]
  exact natDegree_C_mul_X 2 (by norm_num)

/-- From `(2X+1) * G = D * K` conclude `D ∣ G`.

Proof route (encoded below; probes pinned in `CJ_r14.log`):
map to `ℚ[X]` via `Polynomial.map (Int.castRingHom ℚ)`; in `ℚ[X]` the
polynomial `D = X^2+X+1` is irreducible
(`Polynomial.irreducible_of_degree_le_three_of_not_isRoot`, no rational
root since `(2x+1)^2 = -3`), hence prime (`Irreducible.prime`,
instance `DecompositionMonoid (ℚ[X])` confirmed by mini-probe);
`Prime.dvd_or_dvd` on `φ(2X+1) * φ(G) = D * φ(K)`; the branch
`D ∣ φ(2X+1)` is excluded by `natDegree` arithmetic; so `D ∣ φ G`;
descend to `ℤ[X]` by monic division: `G = D * (G /ₘ D) + G %ₘ D`
(`modByMonic_add_div`), map to `ℚ`, subtract — degree of
`φ(G %ₘ D)` is `< 2` (`natDegree_modByMonic_lt`, `D.Monic`) while the
other side has degree `≥ 2` unless `G %ₘ D = 0`, which gives `D ∣ G`
(`modByMonic_eq_zero_iff_dvd`). -/

private lemma D_dvd_of_deriv_rel {G K : ℤ[X]}
    (h : (2 * X + 1) * G = (X ^ 2 + X + 1) * K) : X ^ 2 + X + 1 ∣ G := by
  have hDq : Polynomial.map (Int.castRingHom ℚ) (X ^ 2 + X + 1) = Dq := by simp [φ, Dq]
  have hq : φ (2 * X + 1) * φ G = Dq * φ K := by
    have hmap := congrArg φ h
    simp only [φ, Polynomial.map_mul] at hmap
    rw [hDq] at hmap
    exact hmap
  have hcast : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hndD : natDegree Dq = 2 := by
    simp only [Dq]
    rw [natDegree_add_one]
    refine (natDegree_add_eq_left_of_natDegree_lt ?_).trans (by simp)
    simp
  have hndDz : natDegree (X ^ 2 + X + 1 : ℤ[X]) = 2 := by
    rw [natDegree_add_one]
    refine (natDegree_add_eq_left_of_natDegree_lt ?_).trans (by simp)
    simp
  have hirr : Irreducible Dq := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [hndD]
      decide
    · intro x hx
      have hx' : x ^ 2 + x + 1 = 0 := by
        simpa only [Dq, Polynomial.IsRoot.def, eval_add, eval_pow, eval_X,
          eval_one] using hx
      have h3 : (2 * x + 1) ^ 2 = -3 := by nlinarith
      nlinarith [mul_self_nonneg (2 * x + 1)]
  have hprime : Prime Dq := Irreducible.prime hirr
  have hDq0 : Dq ≠ 0 := Prime.ne_zero hprime
  have hdvd : Dq ∣ φ (2 * X + 1) * φ G := ⟨φ K, hq⟩
  have hnd2 : natDegree (φ (2 * X + 1)) = 1 := by
    simp only [φ]
    rw [Polynomial.natDegree_map_eq_of_injective hcast (2 * X + 1),
      natDegree_add_one, show (2 : ℤ[X]) = C 2 from (C_eq_natCast 2).symm]
    exact natDegree_C_mul_X 2 (by norm_num)
  have hex : ¬Dq ∣ φ (2 * X + 1) := by
    intro hdiv
    obtain ⟨s, hs⟩ := exists_eq_mul_right_of_dvd hdiv
    by_cases hs0 : s = 0
    · subst hs0
      rw [mul_zero] at hs
      have hnd := congrArg natDegree hs
      rw [hnd2, Polynomial.natDegree_zero] at hnd
      omega
    · have hnd := congrArg natDegree hs
      rw [Polynomial.natDegree_mul hDq0 hs0, hndD, hnd2] at hnd
      omega
  obtain hbad | hdiv := Prime.dvd_or_dvd hprime hdvd
  · exact absurd hbad hex
  have hM : Monic (X ^ 2 + X + 1 : ℤ[X]) := by
    rw [show (X ^ 2 + X + 1 : ℤ[X]) = X ^ 2 + (X + 1) from by ring]
    exact monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by simp [natDegree_add_one]))
  have hne1 : (X ^ 2 + X + 1 : ℤ[X]) ≠ 1 := by
    intro hzero
    have he := congrArg (Polynomial.eval 1) hzero
    simp only [eval_add, eval_pow, eval_X, eval_one] at he
    norm_num at he
  have hmod : Dq ∣ φ (G %ₘ (X ^ 2 + X + 1)) := by
    have hident := Polynomial.modByMonic_add_div G (X ^ 2 + X + 1)
    have hcon := congrArg φ hident
    simp only [φ] at hcon
    rw [Polynomial.map_add, Polynomial.map_mul, hDq] at hcon
    simp only [φ] at hdiv
    rw [← hcon] at hdiv
    have heq : (φ (G %ₘ (X ^ 2 + X + 1)) + Dq * φ (G /ₘ (X ^ 2 + X + 1)))
        - Dq * φ (G /ₘ (X ^ 2 + X + 1)) = φ (G %ₘ (X ^ 2 + X + 1)) := by ring
    rw [← heq]
    exact dvd_sub hdiv (dvd_mul_right Dq _)
  by_cases hz : φ (G %ₘ (X ^ 2 + X + 1)) = 0
  · have h0 : G %ₘ (X ^ 2 + X + 1) = 0 :=
      (Polynomial.map_eq_zero_iff hcast).mp hz
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hM).mp h0
  · have hle : natDegree (φ (G %ₘ (X ^ 2 + X + 1))) < 2 := by
      simp only [φ]
      rw [Polynomial.natDegree_map_eq_of_injective hcast (G %ₘ (X ^ 2 + X + 1))]
      have hlt := Polynomial.natDegree_modByMonic_lt G hM hne1
      omega
    obtain ⟨s2, hs2⟩ := exists_eq_mul_right_of_dvd hmod
    have hs2ne : s2 ≠ 0 := fun hz2 => hz (by rw [hs2, hz2, mul_zero])
    have hnd := congrArg natDegree hs2
    rw [Polynomial.natDegree_mul hDq0 hs2ne, hndD] at hnd
    have hcon : False := by omega
    exact hcon.elim

/-- `(X^2+X+1)^2` divides `F n`. -/
lemma D2_dvd_F {n : ℕ} (hn6 : ∃ l, n = 6 * l + 1) : (X ^ 2 + X + 1) ^ 2 ∣ F n := by
  obtain ⟨G, hFG⟩ := exists_eq_mul_right_of_dvd (D_dvd_F hn6)
  obtain ⟨K, hrel⟩ := deriv_relation hn6 hFG
  obtain ⟨K', hGK⟩ := exists_eq_mul_right_of_dvd (D_dvd_of_deriv_rel hrel)
  refine ⟨K', ?_⟩
  rw [hFG, hGK, ← mul_assoc, ← pow_two]

/-! ### Pairwise coprimality of the non-constant factors -/

lemma coprime_X_Y : IsCoprime (X : ℤ[X]) (X + C 1) := by
  refine ⟨-1, 1, ?_⟩
  rw [← show (1 : ℤ[X]) = C 1 from rfl]
  ring

lemma coprime_X_D : IsCoprime (X : ℤ[X]) (X ^ 2 + X + 1) :=
  ⟨-(X + 1), 1, by ring⟩

lemma coprime_Y_D : IsCoprime (X + C 1 : ℤ[X]) (X ^ 2 + X + 1) := by
  refine ⟨-X, 1, ?_⟩
  rw [← show (1 : ℤ[X]) = C 1 from rfl]
  ring

/-! ### Block 1: the factorization identity -/

/-- **Block 1**: for prime `n = 6l+1`, `(X+1)^n - X^n - 1` factors as
`n * X * (X+1) * (X^2+X+1)^2 * E` over `ℤ[X]`. -/
theorem CJ_block1 {n : ℕ} (hn : Nat.Prime n) (hn6 : ∃ l, n = 6 * l + 1) :
    ∃ E : ℤ[X], F n = C (n : ℤ) * X * (X + C 1) * (X ^ 2 + X + 1) ^ 2 * E := by
  have hM0 : X * (X + C 1) * (X ^ 2 + X + 1) ^ 2 ∣ F n := by
    have h1 := IsCoprime.mul_dvd coprime_X_Y
      (X_dvd_F n (by have := hn.two_le; omega)) (X1_dvd_F hn6)
    have hA : IsCoprime (X * (X + C 1) : ℤ[X]) (X ^ 2 + X + 1) :=
      IsCoprime.mul_left coprime_X_D coprime_Y_D
    have hA2 : IsCoprime (X * (X + C 1) : ℤ[X])
        ((X ^ 2 + X + 1) * (X ^ 2 + X + 1)) :=
      IsCoprime.symm
        (IsCoprime.mul_left (IsCoprime.symm hA) (IsCoprime.symm hA))
    have hD2p : (X ^ 2 + X + 1) * (X ^ 2 + X + 1) ∣ F n := by
      rw [← pow_two]
      exact D2_dvd_F hn6
    rw [pow_two]
    exact IsCoprime.mul_dvd hA2 h1 hD2p
  obtain ⟨G, hFG⟩ := exists_eq_mul_right_of_dvd hM0
  have hcn : C (n : ℤ) ∣ G := by
    have hdiv : C (n : ℤ) ∣ X * (X + C 1) * (X ^ 2 + X + 1) ^ 2 * G := by
      rw [← hFG]
      exact n_dvd_F hn
    refine UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors ?_ ?_ hdiv
    · intro h
      apply hn.ne_zero
      have h2 := congrArg (fun p : ℤ[X] => Polynomial.coeff p 0) h
      simp only [Polynomial.coeff_C, Polynomial.coeff_zero] at h2
      exact_mod_cast h2
    · intro d hd1 hd2
      obtain ⟨e, he⟩ := exists_eq_mul_right_of_dvd hd1
      have hd0 : d ≠ 0 := by
        intro h
        rw [h, zero_mul] at he
        apply hn.ne_zero
        have h2 := congrArg (fun p : ℤ[X] => Polynomial.coeff p 0) he
        simp only [Polynomial.coeff_C, Polynomial.coeff_zero] at h2
        exact_mod_cast h2
      have he0 : e ≠ 0 := by
        intro h
        rw [h, mul_zero] at he
        apply hn.ne_zero
        have h2 := congrArg (fun p : ℤ[X] => Polynomial.coeff p 0) he
        simp only [Polynomial.coeff_C, Polynomial.coeff_zero] at h2
        exact_mod_cast h2
      have hnd : natDegree d + natDegree e = 0 := by
        rw [← natDegree_mul hd0 he0, ← he, natDegree_C]
      have hnd0 : natDegree d = 0 := by omega
      obtain ⟨c, hdeq⟩ : ∃ c : ℤ, d = C c :=
        ⟨coeff d 0, Polynomial.eq_C_of_natDegree_eq_zero hnd0⟩
      rw [hdeq] at hd1 hd2
      have hcn' : c ∣ (n : ℤ) := by
        have := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hd1 0
        simpa [Polynomial.coeff_C] using this
      have hv1 : c ∣ (18 : ℤ) := by
        have h := eval_dvd (x := (1 : ℤ)) hd2
        simp only [eval_C, eval_mul, eval_pow, eval_add, eval_X] at h
        norm_num at h
        exact h
      have hv2 : c ∣ (294 : ℤ) := by
        have h := eval_dvd (x := (2 : ℤ)) hd2
        simp only [eval_C, eval_mul, eval_pow, eval_add, eval_X] at h
        norm_num at h
        exact h
      have h6 : c ∣ (6 : ℤ) := by
        have h := dvd_sub hv2 (hv1.mul_right 16)
        simpa using h
      obtain ⟨l, hl⟩ := hn6
      have ha : c ∣ (6 * l + 1 : ℤ) := by
        rw [hl] at hcn'
        exact hcn'
      have hcomb : c ∣ ((6 * l + 1 : ℤ) - l * 6) := dvd_sub ha (h6.mul_left l)
      have heq1 : ((6 * l + 1 : ℤ) - l * 6) = 1 := by ring
      rw [heq1] at hcomb
      rw [hdeq]
      intro hp
      exact Prime.not_isUnit hp (isUnit_C.mpr (isUnit_of_dvd_one hcomb))
  obtain ⟨E, hGE⟩ := exists_eq_mul_right_of_dvd hcn
  refine ⟨E, ?_⟩
  rw [hFG, hGE]
  ring

-- ===== probes for Block 2/3 names (errors non-blocking) =====
#check @Int.natAbs_mul
#check @Int.natAbs_natCast
#check @Int.natAbs_pow
#check @Int.dvd_natAbs
#check @Int.natAbs_eq_zero
#check @padicValNat.pow
#check @padicValNat_self
#check @ZMod.intCast_zmod_eq_zero_iff_dvd
#check @ZMod.pow_card_sub_one_eq_one

/-! ### Block 2: valuation decomposition (univariate core)

Bivariate homogenization is done (`homog_ident`/`CJ_homog` below,
Block 2b); this is the root-channel form the conjecture reduces to: at
an integer `x` whose three factors are all prime to `n`, the n-adic
valuation of `F n` at `x` is exactly `1 + v_n(E x)`. -/

theorem CJ_valuation {n : ℕ} [Fact (Nat.Prime n)]
    {E : ℤ[X]} (hE : F n = C (n : ℤ) * X * (X + C 1) * (X ^ 2 + X + 1) ^ 2 * E)
    (x : ℤ) (hxn : ¬(n : ℤ) ∣ x) (hx1 : ¬(n : ℤ) ∣ (x + 1))
    (hxD : ¬(n : ℤ) ∣ (x ^ 2 + x + 1)) (hE0 : E.eval x ≠ 0) :
    padicValNat n ((F n).eval x).natAbs = 1 + padicValNat n (E.eval x).natAbs := by
  have hn : Nat.Prime n := ‹Fact (Nat.Prime n)›.out
  have hFE : (F n).eval x =
      (n : ℤ) * x * (x + 1) * (x ^ 2 + x + 1) ^ 2 * E.eval x := by
    rw [hE]
    simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_one]
  have hnc : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have hx0 : x ≠ 0 := fun h => hxn (by rw [h]; exact dvd_zero _)
  have hx10 : x + 1 ≠ 0 := fun h => hx1 (by rw [h]; exact dvd_zero _)
  have hD0 : x ^ 2 + x + 1 ≠ 0 := fun h => hxD (by rw [h]; exact dvd_zero _)
  have hF0 : (F n).eval x ≠ 0 := by
    rw [hFE]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hnc hx0) hx10)
      (pow_ne_zero 2 hD0)) hE0
  have hnxN : ¬n ∣ x.natAbs := fun h =>
    hxn ((Int.dvd_natAbs).mp (Int.ofNat_dvd.mpr h))
  have hnx1N : ¬n ∣ (x + 1).natAbs := fun h =>
    hx1 ((Int.dvd_natAbs).mp (Int.ofNat_dvd.mpr h))
  have hnDN : ¬n ∣ (x ^ 2 + x + 1).natAbs := fun h =>
    hxD ((Int.dvd_natAbs).mp (Int.ofNat_dvd.mpr h))
  have hxn0 : x.natAbs ≠ 0 := fun h => hx0 (Int.natAbs_eq_zero.mp h)
  have hx1n0 : (x + 1).natAbs ≠ 0 := fun h => hx10 (Int.natAbs_eq_zero.mp h)
  have hDn0 : (x ^ 2 + x + 1).natAbs ≠ 0 := fun h => hD0 (Int.natAbs_eq_zero.mp h)
  have hEn0 : (E.eval x).natAbs ≠ 0 := fun h => hE0 (Int.natAbs_eq_zero.mp h)
  have hFne : ((F n).eval x).natAbs ≠ 0 := fun h => hF0 (Int.natAbs_eq_zero.mp h)
  have hNA : ((F n).eval x).natAbs =
      n * x.natAbs * (x + 1).natAbs * (x ^ 2 + x + 1).natAbs ^ 2 * (E.eval x).natAbs := by
    rw [hFE]
    simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
  have p0 : n * x.natAbs ≠ 0 := mul_ne_zero hn.ne_zero hxn0
  have p1 : n * x.natAbs * (x + 1).natAbs ≠ 0 := mul_ne_zero p0 hx1n0
  have p2 : n * x.natAbs * (x + 1).natAbs * (x ^ 2 + x + 1).natAbs ^ 2 ≠ 0 :=
    mul_ne_zero p1 (pow_ne_zero 2 hDn0)
  calc
    padicValNat n ((F n).eval x).natAbs
        = padicValNat n
            (n * x.natAbs * (x + 1).natAbs * (x ^ 2 + x + 1).natAbs ^ 2 * (E.eval x).natAbs) := by
      rw [hNA]
    _ = padicValNat n (n * x.natAbs * (x + 1).natAbs * (x ^ 2 + x + 1).natAbs ^ 2)
          + padicValNat n (E.eval x).natAbs := by
      rw [padicValNat.mul p2 hEn0]
    _ = padicValNat n (n * x.natAbs * (x + 1).natAbs)
          + padicValNat n ((x ^ 2 + x + 1).natAbs ^ 2)
          + padicValNat n (E.eval x).natAbs := by
      rw [padicValNat.mul p1 (pow_ne_zero 2 hDn0)]
    _ = padicValNat n (n * x.natAbs * (x + 1).natAbs)
          + 2 * padicValNat n (x ^ 2 + x + 1).natAbs
          + padicValNat n (E.eval x).natAbs := by
      simp only [padicValNat.pow]
    _ = (padicValNat n (n * x.natAbs) + padicValNat n (x + 1).natAbs)
          + 2 * padicValNat n (x ^ 2 + x + 1).natAbs
          + padicValNat n (E.eval x).natAbs := by
      rw [padicValNat.mul p0 hx1n0]
    _ = (padicValNat n n + padicValNat n x.natAbs) + padicValNat n (x + 1).natAbs
          + 2 * padicValNat n (x ^ 2 + x + 1).natAbs
          + padicValNat n (E.eval x).natAbs := by
      rw [padicValNat.mul hn.ne_zero hxn0]
    _ = 1 + padicValNat n (E.eval x).natAbs := by
      rw [padicValNat_self, padicValNat.eq_zero_of_not_dvd hnxN,
        padicValNat.eq_zero_of_not_dvd hnx1N,
        padicValNat.eq_zero_of_not_dvd hnDN]

/-! ### Block 3a: exact derivative + non-liftable root (`n^2 ∣ F'(x)`) -/

/-- The derivative of `F n` is `n * ((X+1)^(n-1) - X^(n-1))` exactly. -/
theorem CJ_deriv (n : ℕ) : derivative (F n) =
    C (n : ℤ) * ((X + C 1) ^ (n - 1) - X ^ (n - 1)) := by
  simp only [F, derivative_sub, derivative_pow, derivative_X_add_C, derivative_X,
    derivative_C, mul_one, sub_zero]
  ring

/-- Non-liftable root: for prime `n` with `x`, `x + 1` both prime to `n`,
`n^2` divides `(F n)'` at `x`. Algebraic core of "Hensel never applies":
every valid root has vanishing derivative mod `n^2`. -/
theorem CJ_nonlift {n : ℕ} (hn : Nat.Prime n) (x : ℤ)
    (h1 : ¬(n : ℤ) ∣ x) (h2 : ¬(n : ℤ) ∣ (x + 1)) :
    (n : ℤ) ^ 2 ∣ (derivative (F n)).eval x := by
  haveI : Fact (Nat.Prime n) := ⟨hn⟩
  rw [CJ_deriv n]
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_add, eval_one]
  have h1z : ((x : ℤ) : ZMod n) ≠ 0 := fun h =>
    h1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have h2z : ((x + 1 : ℤ) : ZMod n) ≠ 0 := fun h =>
    h2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have h1p : ((x : ℤ) : ZMod n) ^ (n - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one h1z
  have h2p : ((x + 1 : ℤ) : ZMod n) ^ (n - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one h2z
  have hA : (n : ℤ) ∣ (x + 1) ^ (n - 1) - 1 := by
    have h : (((x + 1 : ℤ) ^ (n - 1) - 1 : ℤ) : ZMod n) = 0 := by
      rw [Int.cast_sub, Int.cast_one, Int.cast_pow, h2p]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have hB : (n : ℤ) ∣ x ^ (n - 1) - 1 := by
    have h : (((x : ℤ) ^ (n - 1) - 1 : ℤ) : ZMod n) = 0 := by
      rw [Int.cast_sub, Int.cast_one, Int.cast_pow, h1p]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have hdiff : (n : ℤ) ∣ (x + 1) ^ (n - 1) - x ^ (n - 1) := by
    have heq : (x + 1) ^ (n - 1) - x ^ (n - 1)
        = ((x + 1) ^ (n - 1) - 1) - (x ^ (n - 1) - 1) := by ring
    rw [heq]
    exact dvd_sub hA hB
  obtain ⟨k, hk⟩ := hdiff
  refine ⟨k, ?_⟩
  rw [hk]
  ring

/-! ### Block 2b: bivariate homogenization — `E₂(a,b)` and the `P` factorization -/

-- ===== names for this section (surface in this round) =====
#check @Polynomial.natDegree_sub_le
#check @Polynomial.natDegree_pow_le
#check @Polynomial.natDegree_mul
#check @Polynomial.natDegree_X
#check @Polynomial.homogenize_mul
#check @Polynomial.eval_homogenize
#check @MvPolynomial.eval_mul
#check @MvPolynomial.eval_pow
#check @MvPolynomial.eval_add
#check @MvPolynomial.eval_X
#check @MvPolynomial.eval_C
#check @Polynomial.natDegree_pow
#check @MvPolynomial.eval₂_map
#check @MvPolynomial.eval_map
#check @MvPolynomial.C_mul'
#check @div_pow
#check @inv_pow

/-- `F n ≠ 0`: the coefficient of `X^1` in `(X+1)^n - X^n - 1` is `n ≠ 0`. -/
private lemma F_ne_zero {n : ℕ} (hn : Nat.Prime n) : F n ≠ 0 := by
  intro hF0
  have h2 : 2 ≤ n := hn.two_le
  have h1n : 1 ≠ n := by omega
  have h10 : 1 ≠ 0 := by omega
  have hF1 := congrArg (fun p : ℤ[X] => Polynomial.coeff p 1) hF0
  simp only [F, coeff_sub, coeff_X_add_C_pow, coeff_X_pow, coeff_C, Polynomial.coeff_zero,
    one_pow, sub_zero, if_neg h1n, if_neg h10, Nat.choose_one_right] at hF1
  omega

/-- `natDegree (F n) ≤ n` (coarse bound; the leading `X^n` terms cancel but we never
need the exact `n - 1`). -/
private lemma natDegree_F_le (n : ℕ) : Polynomial.natDegree (F n) ≤ n := by
  simp only [F]
  have h1 : Polynomial.natDegree ((X + C 1) ^ n : ℤ[X]) ≤ n :=
    le_trans Polynomial.natDegree_pow_le (by rw [Polynomial.natDegree_X_add_C, Nat.mul_one])
  have h2 : Polynomial.natDegree (X ^ n : ℤ[X]) ≤ n :=
    le_trans Polynomial.natDegree_pow_le (by rw [Polynomial.natDegree_X, Nat.mul_one])
  have h3 : Polynomial.natDegree (C 1 : ℤ[X]) ≤ n := by
    rw [Polynomial.natDegree_C]
    omega
  exact le_trans (Polynomial.natDegree_sub_le _ _) <|
    max_le (le_trans (Polynomial.natDegree_sub_le _ _) (max_le h1 h2)) h3

/-- `X * (X+1) * (X²+X+1)²` is nonzero (evaluate at 1: `1 · 2 · 9 ≠ 0`). -/
private lemma stuff_ne_zero : (X * (X + C 1) * (X ^ 2 + X + 1) ^ 2 : ℤ[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 1) h
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_one] at this
  norm_num at this

/-- `C n` is nonzero for prime `n`. -/
private lemma cn_ne_zero {n : ℕ} (hn : Nat.Prime n) : (C (n : ℤ) : ℤ[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp only [eval_C, eval_zero] at this
  exact hn.ne_zero (by exact_mod_cast this)

/-- Distribute `homogenize` at total degree `n` over the Block-1 factorization.
Splits: `(C n · X)` gets degree 1, `X+1` gets 1, `(X²+X+1)²` gets 4, `E` gets `n-6`
(sum `n`, each at least its `natDegree`). -/
private theorem homog_ident {n : ℕ} (hn : Nat.Prime n) (hn6 : ∃ l, n = 6 * l + 1)
    {E : ℤ[X]} (hE : F n = C (n : ℤ) * X * (X + C 1) * (X ^ 2 + X + 1) ^ 2 * E) :
    Polynomial.homogenize (F n) n =
      MvPolynomial.C (n : ℤ) * MvPolynomial.X 0 * (MvPolynomial.X 0 + MvPolynomial.X 1) *
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2) ^ 2 *
      Polynomial.homogenize E (n - 6) := by
  obtain ⟨l, hl⟩ := hn6
  have h2 : 2 ≤ n := hn.two_le
  have h6 : 6 ≤ n := by omega
  have hcn0 : (C (n : ℤ) : ℤ[X]) ≠ 0 := cn_ne_zero hn
  have hX0 : (X : ℤ[X]) ≠ 0 := by
    intro h; have := congrArg (Polynomial.eval 1) h; simp at this
  have hY0 : (X + C 1 : ℤ[X]) ≠ 0 := by
    intro h; have := congrArg (Polynomial.eval 0) h; simp at this
  have hD0 : (X ^ 2 + X + 1 : ℤ[X]) ≠ 0 := by
    intro h; have := congrArg (Polynomial.eval 0) h; simp at this
  have hD20 : ((X ^ 2 + X + 1) ^ 2 : ℤ[X]) ≠ 0 := pow_ne_zero 2 hD0
  have hstuff0 : (C (n : ℤ) * X * (X + C 1) * (X ^ 2 + X + 1) ^ 2 : ℤ[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hcn0 hX0) hY0) hD20
  have hndF : Polynomial.natDegree (F n) ≤ n := natDegree_F_le n
  have hF0 : F n ≠ 0 := F_ne_zero hn
  have hE0 : E ≠ 0 := fun hE0 => hF0 (by rw [hE, hE0, mul_zero])
  have hndD : Polynomial.natDegree (X ^ 2 + X + 1 : ℤ[X]) = 2 := by
    rw [natDegree_add_one]
    refine (natDegree_add_eq_left_of_natDegree_lt ?_).trans (by simp)
    simp
  have hndD2 : Polynomial.natDegree ((X ^ 2 + X + 1) ^ 2 : ℤ[X]) = 4 := by
    rw [Polynomial.natDegree_pow (X ^ 2 + X + 1) 2, hndD]
  have hndXY : Polynomial.natDegree (C (n : ℤ) * X : ℤ[X]) = 1 := by
    rw [Polynomial.natDegree_mul hcn0 hX0, Polynomial.natDegree_C, Polynomial.natDegree_X]
  have hndY : Polynomial.natDegree (X + C 1 : ℤ[X]) = 1 := Polynomial.natDegree_X_add_C 1
  have hndXYD2 : Polynomial.natDegree (C (n : ℤ) * X * (X + C 1) : ℤ[X]) = 2 := by
    rw [Polynomial.natDegree_mul (mul_ne_zero hcn0 hX0) hY0, hndXY, hndY]
  have hndStuff :
      Polynomial.natDegree (C (n : ℤ) * X * (X + C 1) * (X ^ 2 + X + 1) ^ 2 : ℤ[X]) = 6 := by
    rw [Polynomial.natDegree_mul (mul_ne_zero (mul_ne_zero hcn0 hX0) hY0) hD20,
      hndXYD2, hndD2]
  have hndE : Polynomial.natDegree E ≤ n - 6 := by
    have hmul := Polynomial.natDegree_mul hstuff0 hE0
    rw [hndStuff] at hmul
    rw [hE] at hndF
    rw [hmul] at hndF
    omega
  -- distribute
  rw [hE]
  have h1 := Polynomial.homogenize_mul
    (C (n : ℤ) * X * (X + C 1) * (X ^ 2 + X + 1) ^ 2) E
    (le_of_eq hndStuff) hndE
  rw [show 6 + (n - 6) = n from by omega] at h1
  rw [h1]
  have h2' := Polynomial.homogenize_mul (C (n : ℤ) * X * (X + C 1)) ((X ^ 2 + X + 1) ^ 2)
    (le_of_eq hndXYD2) (le_of_eq hndD2)
  rw [show (2 + 4 : ℕ) = 6 from rfl] at h2'
  rw [h2']
  have h3 := Polynomial.homogenize_mul (C (n : ℤ) * X) (X + C 1)
    (le_of_eq hndXY) (le_of_eq hndY)
  rw [show (1 + 1 : ℕ) = 2 from rfl] at h3
  rw [h3]
  have h4 : Polynomial.homogenize (C (n : ℤ) * X) 1 =
      MvPolynomial.C (n : ℤ) * MvPolynomial.X 0 := by
    rw [Polynomial.homogenize_C_mul, Polynomial.homogenize_X (by norm_num)]
    simp
  have h5 : Polynomial.homogenize (X + C 1 : ℤ[X]) 1 =
      MvPolynomial.X 0 + MvPolynomial.X 1 := by
    simp [MvPolynomial.C_mul']
  have h6t : Polynomial.homogenize (X ^ 2 + X + 1 : ℤ[X]) 2 =
      MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2 := by
    simp [MvPolynomial.C_mul']
  have h7 := Polynomial.homogenize_mul (X ^ 2 + X + 1) (X ^ 2 + X + 1)
    (le_of_eq hndD) (le_of_eq hndD)
  rw [show (2 + 2 : ℕ) = 4 from rfl] at h7
  rw [← pow_two] at h7
  rw [h6t] at h7
  rw [h4, h5, h7,
    pow_two (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2)]

/-- **Block 2b**: the bivariate factorization `P(a,b) = n·a·(a+b)·(a²+ab+b²)²·E₂(a,b)`
with `E₂ a b = (homogenize E (n-6)).eval ![a,b]`. (`E₂` carries one extra factor `b`
vs Gemini's `n·a·b·(a+b)·…·Eₙ` packaging; under `n ∤ b` the valuations agree.
`b ≠ 0` is the conjecture's positivity hypothesis and guards the rational eval bridge.) -/
theorem CJ_homog {n : ℕ} (hn : Nat.Prime n) (hn6 : ∃ l, n = 6 * l + 1) :
    ∃ E2 : ℤ → ℤ → ℤ, ∀ a b : ℤ, b ≠ 0 →
      (a + b) ^ n - a ^ n - b ^ n =
        n * a * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 * E2 a b := by
  obtain ⟨E, hE⟩ := CJ_block1 hn hn6
  have hident := homog_ident hn hn6 hE
  refine ⟨fun a b => MvPolynomial.eval ![a, b] (Polynomial.homogenize E (n - 6)), ?_⟩
  intro a b hb
  have hbridge : MvPolynomial.eval ![a, b] (Polynomial.homogenize (F n) n)
      = (a + b) ^ n - a ^ n - b ^ n := by
    have hndF : Polynomial.natDegree (F n) ≤ n := natDegree_F_le n
    have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hq := Polynomial.eval_homogenize
      (p := (F n).map (Int.castRingHom ℚ)) (n := n)
      (by rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]; exact hndF)
      ![(a : ℚ), (b : ℚ)] hb0
    rw [Polynomial.homogenize_map] at hq
    have hcast : ∀ Q : MvPolynomial (Fin 2) ℤ,
        MvPolynomial.eval ![(a : ℚ), (b : ℚ)] (MvPolynomial.map (Int.castRingHom ℚ) Q)
          = (MvPolynomial.eval ![a, b] Q : ℚ) := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | add p q hp hq2 => simp [hp, hq2]
      | C x => simp
      | mul_X p i hp =>
        simp [hp]
        fin_cases i <;> first | rfl | simp_all
    rw [hcast] at hq
    have hRHS : (map (Int.castRingHom ℚ) (F n)).eval
        (![(a : ℚ), (b : ℚ)] 0 / ![(a : ℚ), (b : ℚ)] 1) * ![(a : ℚ), (b : ℚ)] 1 ^ n
        = (↑a + ↑b) ^ n - ↑a ^ n - ↑b ^ n := by
      simp [F]
      have hsplit : (↑a / ↑b + 1 : ℚ) = (↑a + ↑b) / ↑b := by field_simp
      rw [hsplit, div_pow, div_pow]
      field_simp
      try ring
    rw [hRHS] at hq
    exact_mod_cast hq
  rw [← hbridge, hident]
  simp

/-- **Block 2**: valuation decomposition at the bivariate level: from
`P = n·a·(a+b)·(a²+ab+b²)²·E₂` and the reading-2 coprimality conditions,
`v_n(P) = 1 + v_n(E₂)`. -/

theorem CJ_valuation_P {n : ℕ} [Fact (Nat.Prime n)] {a b E2v : ℤ}
    (hfac : (a + b) ^ n - a ^ n - b ^ n =
      n * a * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 * E2v)
    (hna : ¬(n : ℤ) ∣ a) (hnab : ¬(n : ℤ) ∣ (a + b))
    (hnD : ¬(n : ℤ) ∣ (a ^ 2 + a * b + b ^ 2)) (hE2 : E2v ≠ 0) :
    padicValNat n ((a + b) ^ n - a ^ n - b ^ n).natAbs =
      1 + padicValNat n E2v.natAbs := by
  have hn : Nat.Prime n := ‹Fact (Nat.Prime n)›.out
  have hnc : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have ha0 : a ≠ 0 := fun h => hna (by rw [h]; exact dvd_zero _)
  have hab0 : a + b ≠ 0 := fun h => hnab (by rw [h]; exact dvd_zero _)
  have hD0 : a ^ 2 + a * b + b ^ 2 ≠ 0 := fun h => hnD (by rw [h]; exact dvd_zero _)
  have hnc0 : (n : ℤ).natAbs ≠ 0 := fun h => hnc (Int.natAbs_eq_zero.mp h)
  have haN : a.natAbs ≠ 0 := fun h => ha0 (Int.natAbs_eq_zero.mp h)
  have habN : (a + b).natAbs ≠ 0 := fun h => hab0 (Int.natAbs_eq_zero.mp h)
  have hDN : (a ^ 2 + a * b + b ^ 2).natAbs ≠ 0 := fun h => hD0 (Int.natAbs_eq_zero.mp h)
  have hE2N : E2v.natAbs ≠ 0 := fun h => hE2 (Int.natAbs_eq_zero.mp h)
  have hnaN : ¬n ∣ a.natAbs := fun h =>
    hna ((Int.dvd_natAbs).mp (Int.ofNat_dvd.mpr h))
  have habnN : ¬n ∣ (a + b).natAbs := fun h =>
    hnab ((Int.dvd_natAbs).mp (Int.ofNat_dvd.mpr h))
  have hDnN : ¬n ∣ (a ^ 2 + a * b + b ^ 2).natAbs := fun h =>
    hnD ((Int.dvd_natAbs).mp (Int.ofNat_dvd.mpr h))
  have hP0 : ((a + b) ^ n - a ^ n - b ^ n).natAbs ≠ 0 := by
    have hPne : (a + b) ^ n - a ^ n - b ^ n ≠ 0 := by
      rw [hfac]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hnc ha0) hab0)
        (pow_ne_zero 2 hD0)) hE2
    exact fun h => hPne (Int.natAbs_eq_zero.mp h)
  have hNA : ((a + b) ^ n - a ^ n - b ^ n).natAbs =
      n * a.natAbs * (a + b).natAbs * (a ^ 2 + a * b + b ^ 2).natAbs ^ 2 * E2v.natAbs := by
    rw [hfac]
    simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
  have p0 : n * a.natAbs ≠ 0 := mul_ne_zero hn.ne_zero haN
  have p1 : n * a.natAbs * (a + b).natAbs ≠ 0 := mul_ne_zero p0 habN
  have p2 : n * a.natAbs * (a + b).natAbs * (a ^ 2 + a * b + b ^ 2).natAbs ^ 2 ≠ 0 :=
    mul_ne_zero p1 (pow_ne_zero 2 hDN)
  calc
    padicValNat n ((a + b) ^ n - a ^ n - b ^ n).natAbs
        = padicValNat n
            (n * a.natAbs * (a + b).natAbs * (a ^ 2 + a * b + b ^ 2).natAbs ^ 2 * E2v.natAbs) := by
      rw [hNA]
    _ = padicValNat n (n * a.natAbs * (a + b).natAbs * (a ^ 2 + a * b + b ^ 2).natAbs ^ 2)
          + padicValNat n E2v.natAbs := by
      rw [padicValNat.mul p2 hE2N]
    _ = padicValNat n (n * a.natAbs * (a + b).natAbs)
          + padicValNat n ((a ^ 2 + a * b + b ^ 2).natAbs ^ 2)
          + padicValNat n E2v.natAbs := by
      rw [padicValNat.mul p1 (pow_ne_zero 2 hDN)]
    _ = padicValNat n (n * a.natAbs * (a + b).natAbs)
          + 2 * padicValNat n (a ^ 2 + a * b + b ^ 2).natAbs
          + padicValNat n E2v.natAbs := by
      simp only [padicValNat.pow]
    _ = (padicValNat n (n * a.natAbs) + padicValNat n (a + b).natAbs)
          + 2 * padicValNat n (a ^ 2 + a * b + b ^ 2).natAbs
          + padicValNat n E2v.natAbs := by
      rw [padicValNat.mul p0 habN]
    _ = (padicValNat n n + padicValNat n a.natAbs) + padicValNat n (a + b).natAbs
          + 2 * padicValNat n (a ^ 2 + a * b + b ^ 2).natAbs
          + padicValNat n E2v.natAbs := by
      rw [padicValNat.mul hn.ne_zero haN]
    _ = 1 + padicValNat n E2v.natAbs := by
      rw [padicValNat_self, padicValNat.eq_zero_of_not_dvd hnaN,
        padicValNat.eq_zero_of_not_dvd habnN,
        padicValNat.eq_zero_of_not_dvd hDnN]

/-! ### Block 3b: fiber-constancy — the screen's exhaustiveness justification -/

-- ===== names for this section (surface in this round) =====
#check @add_pow
#check @Finset.sum_sub_distrib
#check @Finset.dvd_sum
#check @Finset.sum_range_succ
#check @Finset.sum_range_succ'
#check @mul_pow
#check @Nat.choose_symm

/-- `F'` evaluated: `n·((x+1)^(n-1) − x^(n-1))`. Plan gloss: with
`q(y) = (y^(n-1) − 1)/n` (an integer when `n ∣ y^(n-1) − 1`, i.e. `n ∤ y`),
this is exactly `F'(x) = n²(q(x+1) − q(x))`. -/
theorem CJ_fprime {n : ℕ} (x : ℤ) :
    (derivative (F n)).eval x = (n : ℤ) * ((x + 1) ^ (n - 1) - x ^ (n - 1)) := by
  rw [CJ_deriv n]
  simp [eval_mul, eval_sub, eval_pow, eval_add, eval_X, eval_C]

/-- **Fiber-constancy**: if `n² ∣ F'(x₀)` (guaranteed at every valid root by
`CJ_nonlift`), then `n³ ∣ F(x₀ + n·t) − F(x₀)` for all integers `t` — `F` is
constant mod `n³` along each fiber `x ≡ x₀ (mod n)`, so one representative per
root is exhaustive over all pairs `(a,b)`. -/
theorem CJ_fiber {n : ℕ} [Fact (Nat.Prime n)] {x₀ t : ℤ}
    (hF' : (n : ℤ) ^ 2 ∣ (derivative (F n)).eval x₀) :
    (n : ℤ) ^ 3 ∣ (F n).eval (x₀ + n * t) - (F n).eval x₀ := by
  obtain ⟨m, hm⟩ := hF'
  have hn : Nat.Prime n := ‹Fact (Nat.Prime n)›.out
  have h2 : 2 ≤ n := hn.two_le
  simp only [F, eval_sub, eval_add, eval_pow, eval_X, eval_C]
  have heq : (x₀ + n * t + 1) ^ n - (x₀ + n * t) ^ n - 1 - ((x₀ + 1) ^ n - x₀ ^ n - 1)
      = (x₀ + n * t + 1) ^ n - (x₀ + n * t) ^ n - (x₀ + 1) ^ n + x₀ ^ n := by ring
  rw [heq]
  have hA : ((x₀ + 1) + n * t) ^ n
      = ∑ m ∈ Finset.range (n + 1), (x₀ + 1) ^ m * (n * t) ^ (n - m) * n.choose m := by
    rw [add_pow]
  have hB : (x₀ + n * t) ^ n
      = ∑ m ∈ Finset.range (n + 1), x₀ ^ m * (n * t) ^ (n - m) * n.choose m := by
    rw [add_pow]
  rw [show x₀ + n * t + 1 = (x₀ + 1) + n * t from by ring, hA, hB]
  rw [show (x₀ + 1) ^ n = (x₀ + 1) ^ n * (n * t) ^ (n - n) * n.choose n from by
      simp [Nat.choose_self],
    show x₀ ^ n = x₀ ^ n * (n * t) ^ (n - n) * n.choose n from by simp [Nat.choose_self]]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ]
  have rearr : ∀ a b c d : ℤ, (a + b) - c + d = a + (b - c + d) := by intros; ring
  rw [rearr]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, mul_one]
  have hbit0 : ∀ u v : ℤ, (u - v) - u + v = 0 := by intros; ring
  rw [hbit0, add_zero]
  refine Finset.dvd_sum ?_
  intro i hi
  have hib : i < n := Finset.mem_range.mp hi
  by_cases h0 : i = 0
  · rw [h0, pow_zero, pow_zero]
    simp
  · by_cases hlast : i = n - 1
    · rw [hlast, Nat.choose_symm (by omega),
        show n - (n - 1) = 1 from by omega, Nat.choose_one_right, pow_one]
      have key2 : (x₀ + 1) ^ (n - 1) * (n * t) * n - x₀ ^ (n - 1) * (n * t) * n
          = (n * t) * (derivative (F n)).eval x₀ := by
        rw [CJ_fprime]
        ring
      rw [key2, hm]
      exact ⟨t * m, by ring⟩
    · have h1 : 1 ≤ i := by omega
      have hle2 : i ≤ n - 2 := by omega
      have hchoose : n ∣ n.choose i := hn.dvd_choose_self (by omega) hib
      obtain ⟨c, hc⟩ := hchoose
      rw [hc, mul_pow]
      simp only [Nat.cast_mul]
      have hsplit : (n : ℤ) ^ (n - i) = (n : ℤ) ^ 2 * (n : ℤ) ^ ((n - i) - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit]
      refine ⟨c * n ^ ((n - i) - 2) * t ^ (n - i) * ((x₀ + 1) ^ i - x₀ ^ i), ?_⟩
      ring

/-! ### Block 4: verifier contract — counterexample ⟺ `n² ∣ E₂` -/

/-- **Block 4a**: under the reading-2 coprimality conditions, a counterexample
(`v_n(P) ≥ 3`) at a valid pair exists if and only if `n²` divides the
homogenized cofactor `E₂` — the exact target the finite screen's j-test checks. -/
theorem CJ_witness_iff {n : ℕ} [Fact (Nat.Prime n)] {a b E2v : ℤ}
    (hfac : (a + b) ^ n - a ^ n - b ^ n =
      n * a * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 * E2v)
    (hna : ¬(n : ℤ) ∣ a) (hnab : ¬(n : ℤ) ∣ (a + b))
    (hnD : ¬(n : ℤ) ∣ (a ^ 2 + a * b + b ^ 2)) (hE2 : E2v ≠ 0) :
    (3 ≤ padicValNat n ((a + b) ^ n - a ^ n - b ^ n).natAbs) ↔ (n : ℤ) ^ 2 ∣ E2v := by
  rw [CJ_valuation_P hfac hna hnab hnD hE2]
  have hE2N : E2v.natAbs ≠ 0 := fun h => hE2 (Int.natAbs_eq_zero.mp h)
  constructor
  · intro h
    have h2 : 2 ≤ padicValNat n E2v.natAbs := by omega
    have hd : n ^ 2 ∣ E2v.natAbs :=
      (padicValNat_dvd_iff_le hE2N).mpr h2
    have hcast : (n : ℤ) ^ 2 = ↑(n ^ 2) := (Nat.cast_pow n 2).symm
    rw [hcast]
    exact Int.dvd_natAbs.mp (Int.ofNat_dvd.mpr hd)
  · intro h
    have hcast : (n : ℤ) ^ 2 = ↑(n ^ 2) := (Nat.cast_pow n 2).symm
    rw [hcast] at h
    have hd : n ^ 2 ∣ E2v.natAbs := Int.ofNat_dvd.mp (Int.dvd_natAbs.mpr h)
    have h2 : 2 ≤ padicValNat n E2v.natAbs :=
      (padicValNat_dvd_iff_le hE2N).mp hd
    omega

-- ===== names for the verifier core =====
#check @Int.ediv_mul_cancel
#check @Int.mul_ediv_cancel

/-- The screen's polynomial as an exact integer: `f(x) = ((x+1)^n - x^n - 1)/n`
(`n ∣ F(x)` for every integer `x`, so the `ℤ` division is exact). -/
def fInt (n : ℕ) (x : ℤ) : ℤ := ((x + 1) ^ n - x ^ n - 1) / (n : ℤ)

/-- `fInt` is genuinely `F/n`: multiplying back recovers `(x+1)^n - x^n - 1`. -/
lemma fInt_eq {n : ℕ} (hn : Nat.Prime n) (x : ℤ) :
    fInt n x * n = (x + 1) ^ n - x ^ n - 1 := by
  have hd : (n : ℤ) ∣ (x + 1) ^ n - x ^ n - 1 := by
    have h := eval_dvd (x := x) (n_dvd_F hn)
    simpa only [F, eval_sub, eval_add, eval_pow, eval_X, eval_C] using h
  show ((x + 1) ^ n - x ^ n - 1) / (n : ℤ) * n = _
  exact Int.ediv_mul_cancel hd

/-- **Mirror lemma** (the screen's half-range cut): `fInt n (n-1-x) ≡ fInt n x`
(`mod n`) for `x ∈ [0, n-1]`, `n = 6l+1` prime. Exact equality is FALSE
(numerators differ by a multiple of `n²`); the congruence is what the
screen needs: root-ness (`F ≡ 0 mod n²`) and `j = F/n² mod n` transfer
across the mirror. Proof: `(m+1) = -x` exactly so `(m+1)^n = -x^n`, while
`m = n + (-(x+1))` expands by `add_pow` with every term but the head
`n²`-divisible; then cancel `n` from `(fInt m - fInt x) * n = n * (n * K)`. -/
lemma fInt_mirror {n : ℕ} (hn : Nat.Prime n) {l : ℕ} (hn6 : n = 6 * l + 1)
    {x : ℕ} (hx : x ≤ n - 1) :
    (n : ℤ) ∣ fInt n (n - 1 - x : ℕ) - fInt n x := by
  have h1n : 1 ≤ n := by omega
  have hcast : ((n : ℤ) - 1 - (x : ℤ)) = ((n - 1 - x : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : x ≤ n - 1), Nat.cast_sub h1n, Nat.cast_one]
  have key : ((n - 1 - x : ℕ) : ℤ) + 1 = -(x : ℤ) := by
    have hcast' : ((n - 1 - x : ℕ) : ℤ) = (n : ℤ) - 1 - (x : ℤ) := hcast.symm
    rw [hcast']; ring
  have hbase : ((n - 1 - x : ℕ) : ℤ) = (n : ℤ) + (-((x : ℤ) + 1)) := by
    have hcast' : ((n - 1 - x : ℕ) : ℤ) = (n : ℤ) - 1 - (x : ℤ) := hcast.symm
    rw [hcast']; ring
  -- `m^n + (x+1)^n` is `n²`-divisible: head cancels, rest has `n²`
  have hsum : (n : ℤ) ^ 2 ∣ ((n - 1 - x : ℕ) : ℤ) ^ n + ((x : ℤ) + 1) ^ n := by
    rw [hbase, add_pow]
    sorry
  -- `F(m) - F(x) = -(m^n + (x+1)^n)`, then cancel `n`
  have hF1 := fInt_eq hn ((n - 1 - x : ℕ) : ℤ)
  have hF2 := fInt_eq hn (x : ℤ)
  sorry

-- #print axioms for the Block-1/2/3 declarations
#print axioms CJ.CJ_block1
#print axioms CJ.D_dvd_F
#print axioms CJ.X_dvd_F
#print axioms CJ.X1_dvd_F
#print axioms CJ.n_dvd_F
#print axioms CJ.D2_dvd_F
#print axioms CJ.CJ_valuation
#print axioms CJ.CJ_deriv
#print axioms CJ.CJ_nonlift
#print axioms CJ.CJ_homog
#print axioms CJ.CJ_valuation_P
#print axioms CJ.CJ_fprime
#print axioms CJ.CJ_fiber
#print axioms CJ.CJ_witness_iff
#print axioms CJ.fInt_eq

end CJ
