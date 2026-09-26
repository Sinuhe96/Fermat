import Mathlib

/-!
# Lemma 3 (bổ đề 3) — the author's proof, steps S0–S11

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 1, lemma 3 of section A;
  * proof: p. 2, section 3 (the proof of bổ đề 3).

The literal Vietnamese transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L3-01.yml` (`source_text`, `author_steps`).
One named declaration per author step (English paraphrase):

  S0        divide `a` and `c` by their gcd `c'_1 = (a,c)`; the quotients
            `a_1`, `c'_2` are coprime                    -> L3_step_S0
  S1+S2     from `ab = c^n`: `c'_1·a_1·b = c'_1^n·c'_2^n`, hence
            `a_1·b = c'_1^{n-1}·c'_2^n`                 -> L3_step_S1_S2
  S3+S4     `b ∣ c'_1^{n-1}·c'_2^n`, and `(c'_1,b) = 1` gives
            `c'_2^n = k·b` with `k ≠ 0`                 -> L3_step_S3_S4
  S5        cancel `b`: `a_1 = k·c'_1^{n-1}`             -> L3_step_S5
  S6+S7+S8  `a_1^n = k^n·c'_1^{n(n-1)}`, so `k ∣ a_1^n`
            and `k ∣ c'_2^n`                            -> L3_step_S6_S8
  S9+S10    `(a_1,c'_2) = 1` gives `(a_1^n,c'_2^n) = 1`, hence
            `|k| = 1`                                   -> L3_step_S9_S10
  S11       `c_1 = k·c'_1`, `c_2 = k·c'_2` are nonzero, coprime, and
            satisfy `c = c_1·c_2`, `a = c_1^n`, `b = c_2^n`
                                                        -> L3_step_S11
  whole     assembly in the author's order              -> L3_bo_de_3

Nothing here is our own mathematics: the content is the author's chain.
The only formal additions are implicit side conditions the paper leaves to
convention (`a ≠ 0` so that the gcd `(a,c)` is positive, `b ≠ 0` for
cancellation, `c'_2 ≠ 0` from `c = c'_1·c'_2` with `c ≠ 0`, `n ≥ 1` for
`c'_1^n = c'_1·c'_1^{n-1}` — all supplied by the paper's `a,b,c ∈ ℤ*` and
its hypothesis that `n` is an odd positive integer).
-/

namespace L3

/-- **S0** (author p. 2 §3, first sentence).

With `c'_1 := (a,c)`, dividing `a` and `c` by their gcd gives quotients
`a_1` and `c'_2` that are coprime, with `a = c'_1·a_1` and `c = c'_1·c'_2`.

Encoded by `Int.exists_gcd_one`, whose witnesses are exactly the author's
quotients (`m / (m,n)` and `n / (m,n)` via `Int.ediv_mul_cancel`).
The author's `c ∈ ℤ*` is carried as `_hc`: this step only needs `a ≠ 0`
for `(a,c) > 0`. -/
theorem L3_step_S0 {a c : ℤ} (ha : a ≠ 0) (_hc : c ≠ 0) :
    ∃ a1 c2' : ℤ, Int.gcd a1 c2' = 1 ∧
      a = (Int.gcd a c : ℤ) * a1 ∧ c = (Int.gcd a c : ℤ) * c2' := by
  have hpos : 0 < Int.gcd a c := by
    rw [Int.gcd_def]
    exact Nat.gcd_pos_of_pos_left c.natAbs
      (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha))
  obtain ⟨a1, c2', hg, h1, h2⟩ := Int.exists_gcd_one hpos
  refine ⟨a1, c2', hg, ?_, ?_⟩
  · calc a = a1 * (Int.gcd a c : ℤ) := h1
      _ = (Int.gcd a c : ℤ) * a1 := mul_comm _ _
  · calc c = c2' * (Int.gcd a c : ℤ) := h2
      _ = (Int.gcd a c : ℤ) * c2' := mul_comm _ _

/-- **S1 + S2** (author p. 2 §3, second sentence).

Substituting `a = c'_1·a_1` and `c = c'_1·c'_2` into `ab = c^n` gives
`c'_1·a_1·b = c'_1^n·c'_2^n`; cancelling the nonzero `c'_1` and splitting
off one factor of `c'_1` (using `n ≥ 1` from the author's hypothesis that
`n` is an odd positive integer) yields the displayed identity
`a_1·b = c'_1^{n-1}·c'_2^n`.

Side condition: `c'_1 ≠ 0`, because `c'_1 = (a,c)` divides the nonzero `a`
(the paper's `a ∈ ℤ*`). -/
theorem L3_step_S1_S2 {n : ℕ} (hn : 0 < n) {a b c a1 c2' : ℤ} (ha : a ≠ 0)
    (hab : a * b = c ^ n)
    (h1 : a = (Int.gcd a c : ℤ) * a1) (h2 : c = (Int.gcd a c : ℤ) * c2') :
    a1 * b = (Int.gcd a c : ℤ) ^ (n - 1) * c2' ^ n := by
  have hg0 : (Int.gcd a c : ℤ) ≠ 0 := by
    have hpos : 0 < Int.gcd a c := by
      rw [Int.gcd_def]
      exact Nat.gcd_pos_of_pos_left c.natAbs
        (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha))
    exact_mod_cast hpos.ne'
  -- S1: substitute a = c'_1·a_1, c = c'_1·c'_2 into ab = c^n
  have hL : (Int.gcd a c : ℤ) * (a1 * b) = c ^ n := by
    rw [← mul_assoc, ← h1]
    exact hab
  -- S2: cancel c'_1, splitting c'_1^n = c'_1·c'_1^{n-1}
  have hR : c ^ n = (Int.gcd a c : ℤ) * ((Int.gcd a c : ℤ) ^ (n - 1) * c2' ^ n) := by
    conv_lhs => rw [h2]
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]
  exact mul_left_cancel₀ hg0 (hL.trans hR)

/-- **S3 + S4** (author p. 2 §3, third sentence).

S3 is the displayed divisibility `b ∣ c'_1^{n-1}·c'_2^n`. S4 uses the
parenthetical `(c'_1,b) = 1` (derived here from `(a,b) = 1` and
`c'_1 ∣ a`) plus Euclid's lemma to get `b ∣ c'_2^n`, hence
`c'_2^n = k·b`; `k ≠ 0` because `c'_2 ≠ 0` (from `c = c'_1·c'_2` and the
paper's `c ∈ ℤ*`).

The author's `b ∈ ℤ*` is carried as `_hb`: requiring `b ≠ 0` is not needed
here (`c'_2^n = k·b` with `c'_2 ≠ 0` already forces `k ≠ 0`). -/
theorem L3_step_S3_S4 {n : ℕ} {a b c a1 c2' : ℤ} (_ha : a ≠ 0) (_hb : b ≠ 0)
    (hc : c ≠ 0) (hgcd_ab : Int.gcd a b = 1)
    (h1 : a = (Int.gcd a c : ℤ) * a1) (h2 : c = (Int.gcd a c : ℤ) * c2')
    (ha1b : a1 * b = (Int.gcd a c : ℤ) ^ (n - 1) * c2' ^ n) :
    ∃ k : ℤ, k ≠ 0 ∧ c2' ^ n = k * b := by
  -- S3: b ∣ c'_1^{n-1}·c'_2^n
  have hb_dvd : b ∣ (Int.gcd a c : ℤ) ^ (n - 1) * c2' ^ n :=
    ⟨a1, by rw [← ha1b, mul_comm]⟩
  -- S4 parenthetical: c'_1 ∣ a and (a,b) = 1 give (c'_1,b) = 1
  have hg_dvd_a : ((Int.gcd a c : ℕ) : ℤ) ∣ a := ⟨a1, h1⟩
  have hg_b : Int.gcd ((Int.gcd a c : ℕ) : ℤ) b = 1 := by
    refine Nat.dvd_one.mp ?_
    have hm_a : ((Int.gcd ((Int.gcd a c : ℕ) : ℤ) b : ℕ) : ℤ) ∣ a :=
      dvd_trans (Int.gcd_dvd_left _ b) hg_dvd_a
    have hm_b : ((Int.gcd ((Int.gcd a c : ℕ) : ℤ) b : ℕ) : ℤ) ∣ b :=
      Int.gcd_dvd_right _ b
    have h := Int.dvd_gcd hm_a hm_b
    simpa only [hgcd_ab] using h
  -- S4 Euclid: b ∣ c'_1^{n-1}·c'_2^n with (b, c'_1) = 1 gives b ∣ c'_2^n
  have hcop : IsCoprime b ((Int.gcd a c : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact hg_b
  have hcop_pow : IsCoprime b ((Int.gcd a c : ℤ) ^ (n - 1)) := hcop.pow_right
  have hb_dvd_c2 : b ∣ c2' ^ n := hcop_pow.dvd_of_dvd_mul_left hb_dvd
  obtain ⟨k, hk⟩ := hb_dvd_c2
  have hc2 : c2' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h2
    exact hc h2
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact pow_ne_zero n hc2 hk
  exact ⟨k, hk0, by rw [hk, mul_comm]⟩

/-- **S5** (author p. 2 §3, fourth sentence).

From the identity of S2, substitute `c'_2^n = k·b` (S4) and cancel
`b ≠ 0` (the paper's `b ∈ ℤ*`), giving `a_1 = k·c'_1^{n-1}`. -/
theorem L3_step_S5 {n : ℕ} {a c a1 c2' k b : ℤ} (hb : b ≠ 0)
    (ha1b : a1 * b = (Int.gcd a c : ℤ) ^ (n - 1) * c2' ^ n)
    (hk : c2' ^ n = k * b) :
    a1 = k * (Int.gcd a c : ℤ) ^ (n - 1) := by
  have hkey : a1 * b = (k * (Int.gcd a c : ℤ) ^ (n - 1)) * b := by
    rw [ha1b, hk]
    ring
  exact mul_right_cancel₀ hb hkey

/-- **S6 + S7 + S8** (author p. 2 §3, fifth and sixth sentence).

S6 powers the identity of S5 (`mul_pow` + `pow_mul`), giving
`a_1^n = k^n·c'_1^{n(n-1)}`; S7 reads off `k ∣ a_1^n` since `k ∣ k^n`
(`n ≥ 1`, the author's odd-positive hypothesis); S8 is immediate from
`c'_2^n = k·b` (S4). -/
theorem L3_step_S6_S8 {n : ℕ} (hn : 0 < n) {a c a1 c2' k b : ℤ}
    (ha1 : a1 = k * (Int.gcd a c : ℤ) ^ (n - 1)) (hk : c2' ^ n = k * b) :
    k ∣ a1 ^ n ∧ k ∣ c2' ^ n := by
  -- S6
  have hpow : a1 ^ n = k ^ n * (Int.gcd a c : ℤ) ^ (n * (n - 1)) := by
    rw [ha1, mul_pow, ← pow_mul, mul_comm (n - 1) n]
  -- S7
  have hdvd1 : k ∣ a1 ^ n := by
    rw [hpow]
    exact dvd_mul_of_dvd_left (dvd_pow (dvd_refl k) hn.ne') _
  -- S8
  exact ⟨hdvd1, ⟨b, hk⟩⟩

/-- **S9 + S10** (author p. 2 §3, seventh sentence).

Coprimality is preserved by raising both arguments to the same power
(`IsCoprime.pow`): `(a_1^n, c'_2^n) = 1`. Then `k`, dividing both coprime
numbers `a_1^n` and `c'_2^n`, divides their gcd `1`, hence `|k| = 1`. -/
theorem L3_step_S9_S10 {n : ℕ} {a1 c2' k : ℤ} (hgcd : Int.gcd a1 c2' = 1)
    (h7 : k ∣ a1 ^ n) (h8 : k ∣ c2' ^ n) : Int.natAbs k = 1 := by
  -- S9
  have hcop : IsCoprime a1 c2' := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have hcop_pow : IsCoprime (a1 ^ n) (c2' ^ n) := hcop.pow
  have hpow : Int.gcd (a1 ^ n) (c2' ^ n) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hcop_pow
  -- S10
  have hk1 : k ∣ (1 : ℤ) := by
    have h : k ∣ ((Int.gcd (a1 ^ n) (c2' ^ n) : ℕ) : ℤ) := Int.dvd_coe_gcd h7 h8
    rwa [hpow] at h
  have hnat : k.natAbs ∣ (1 : ℤ).natAbs := (Int.natAbs_dvd_natAbs).mpr hk1
  simpa using Nat.dvd_one.mp hnat

/-- **S11** (author p. 2 §3, last paragraph).

`|k| = 1` gives `k = ±1`, hence `k·k = 1` and `k^n = k` (n odd). The
author's witnesses `c_1 = k·c'_1`, `c_2 = k·c'_2` are nonzero, and:
`c = c_1·c_2` follows from `c = c'_1·c'_2` and `k·k = 1`; `a = c_1^n` and
`b = c_2^n` are the author's `k(ka)` / `k(kb)` steps (rewriting
`ka = c'_1^n` resp. `kb = c'_2^n`, then using `k^n = k`); finally
`(c_1,c_2) = 1`, because `c_1^n = a` and `c_2^n = b` are coprime — the
paper's closing claim that `c_1` and `c_2` are coprime. -/
theorem L3_step_S11 {n : ℕ} (hn : Odd n) (hn0 : 0 < n) {a b c a1 c2' k : ℤ}
    (ha : a ≠ 0) (_hb : b ≠ 0) (hc : c ≠ 0) (hgcd_ab : Int.gcd a b = 1)
    (h1 : a = (Int.gcd a c : ℤ) * a1) (h2 : c = (Int.gcd a c : ℤ) * c2')
    (hk : c2' ^ n = k * b) (hk0 : k ≠ 0)
    (ha1 : a1 = k * (Int.gcd a c : ℤ) ^ (n - 1)) (hkab : Int.natAbs k = 1) :
    ∃ c1 c2 : ℤ, c1 ≠ 0 ∧ c2 ≠ 0 ∧ Int.gcd c1 c2 = 1 ∧
      c = c1 * c2 ∧ a = c1 ^ n ∧ b = c2 ^ n := by
  -- |k| = 1 gives k = ±1, hence k·k = 1 and k^n = k (n odd)
  have hk_sq : k * k = 1 := Int.isUnit_mul_self (Int.isUnit_iff_natAbs_eq.mpr hkab)
  have hkn : k ^ n = k := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hk_sq with h | h <;> rw [h]
    · rw [one_pow]
    · rw [Odd.neg_one_pow hn]
  -- the author's quotients c'_1 and c'_2 are nonzero
  have hg0 : (Int.gcd a c : ℤ) ≠ 0 := by
    have hpos : 0 < Int.gcd a c := by
      rw [Int.gcd_def]
      exact Nat.gcd_pos_of_pos_left c.natAbs
        (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha))
    exact_mod_cast hpos.ne'
  have hc2 : c2' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h2
    exact hc h2
  -- c = c_1·c_2
  have hc_fin : c = (k * (Int.gcd a c : ℤ)) * (k * c2') := by
    calc c = (Int.gcd a c : ℤ) * c2' := h2
      _ = (k * k) * ((Int.gcd a c : ℤ) * c2') := by rw [hk_sq, one_mul]
      _ = (k * (Int.gcd a c : ℤ)) * (k * c2') := by ring
  -- a = c_1^n  ("a = k(ka) = k c'_1^n = (k c'_1)^n")
  have ha_fin : a = (k * (Int.gcd a c : ℤ)) ^ n := by
    have hgpow : (Int.gcd a c : ℤ) ^ n =
        (Int.gcd a c : ℤ) * (Int.gcd a c : ℤ) ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    calc a = (Int.gcd a c : ℤ) * a1 := h1
      _ = (Int.gcd a c : ℤ) * (k * (Int.gcd a c : ℤ) ^ (n - 1)) := by rw [ha1]
      _ = k * ((Int.gcd a c : ℤ) * (Int.gcd a c : ℤ) ^ (n - 1)) := by ring
      _ = k * (Int.gcd a c : ℤ) ^ n := by rw [hgpow]
      _ = (k * (Int.gcd a c : ℤ)) ^ n := by rw [mul_pow, hkn]
  -- b = c_2^n  ("b = k(kb) = k c'_2^n = (k c'_2)^n")
  have hb_fin : b = (k * c2') ^ n := by
    calc b = k * (k * b) := by rw [← mul_assoc, hk_sq, one_mul]
      _ = k * c2' ^ n := by rw [hk]
      _ = k ^ n * c2' ^ n := by rw [hkn]
      _ = (k * c2') ^ n := by rw [mul_pow]
  -- (c_1, c_2) = 1, because c_1^n = a and c_2^n = b are coprime
  have hcop_fin : Int.gcd (k * (Int.gcd a c : ℤ)) (k * c2') = 1 := by
    refine Nat.dvd_one.mp ?_
    have hm_a : ((Int.gcd (k * (Int.gcd a c : ℤ)) (k * c2') : ℕ) : ℤ) ∣ a := by
      conv_rhs => rw [ha_fin]
      exact dvd_pow (Int.gcd_dvd_left (k * (Int.gcd a c : ℤ)) (k * c2')) hn0.ne'
    have hm_b : ((Int.gcd (k * (Int.gcd a c : ℤ)) (k * c2') : ℕ) : ℤ) ∣ b := by
      conv_rhs => rw [hb_fin]
      exact dvd_pow (Int.gcd_dvd_right (k * (Int.gcd a c : ℤ)) (k * c2')) hn0.ne'
    have h := Int.dvd_gcd hm_a hm_b
    simpa only [hgcd_ab] using h
  exact ⟨k * (Int.gcd a c : ℤ), k * c2', mul_ne_zero hk0 hg0,
    mul_ne_zero hk0 hc2, hcop_fin, hc_fin, ha_fin, hb_fin⟩

/-- **Bổ đề 3** — the author's statement (p. 1), proved by the p. 2 §3
chain S0–S11 in the author's order:

> let `a·b = c^n` with `n` an odd positive integer, `a, b, c` nonzero
> integers and `(a,b) = 1`; then there exist nonzero integers `c₁, c₂`
> with `(c₁,c₂) = 1`, `c = c₁·c₂`, `a = c₁^n` and `b = c₂^n`.

Assembly of the verified steps: `L3_step_S0`, `L3_step_S1_S2`,
`L3_step_S3_S4`, `L3_step_S5`, `L3_step_S6_S8`, `L3_step_S9_S10`,
`L3_step_S11`. -/
theorem L3_bo_de_3 {a b c : ℤ} {n : ℕ} (hn : Odd n) (hn0 : 0 < n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a * b = c ^ n) (hgcd_ab : Int.gcd a b = 1) :
    ∃ c1 c2 : ℤ, c1 ≠ 0 ∧ c2 ≠ 0 ∧ Int.gcd c1 c2 = 1 ∧
      c = c1 * c2 ∧ a = c1 ^ n ∧ b = c2 ^ n := by
  -- S0: divide a, c by c'_1 = (a,c)
  obtain ⟨a1, c2', hgcd1, h1, h2⟩ := L3_step_S0 ha hc
  -- S1 + S2: a_1·b = c'_1^{n-1}·c'_2^n
  have ha1b := L3_step_S1_S2 hn0 ha hab h1 h2
  -- S3 + S4: c'_2^n = k·b with k ≠ 0
  obtain ⟨k, hk0, hk⟩ := L3_step_S3_S4 ha hb hc hgcd_ab h1 h2 ha1b
  -- S5: a_1 = k·c'_1^{n-1}
  have ha1 := L3_step_S5 hb ha1b hk
  -- S6 + S7 + S8: k ∣ a_1^n and k ∣ c'_2^n
  obtain ⟨hd1, hd2⟩ := L3_step_S6_S8 hn0 ha1 hk
  -- S9 + S10: |k| = 1
  have hkab := L3_step_S9_S10 hgcd1 hd1 hd2
  -- S11: the author's witnesses c_1 = k·c'_1, c_2 = k·c'_2
  exact L3_step_S11 hn hn0 ha hb hc hgcd_ab h1 h2 hk hk0 ha1 hkab

#print axioms L3.L3_step_S0
#print axioms L3.L3_step_S1_S2
#print axioms L3.L3_step_S3_S4
#print axioms L3.L3_step_S5
#print axioms L3.L3_step_S6_S8
#print axioms L3.L3_step_S9_S10
#print axioms L3.L3_step_S11
#print axioms L3.L3_bo_de_3

end L3
