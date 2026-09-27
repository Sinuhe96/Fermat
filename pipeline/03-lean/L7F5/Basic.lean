import Mathlib
import L5.Basic
import L7F3.Basic
import L7F4.Basic

/-!
# Lemma 7 (bổ đề 7) — n ≡ 1 (mod 6) (chunk L7-FRAG-05)

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 2 top, "n ≡ 1 (mod 6)";
  * proof: p. 5 §7, the bullet "Vì n là số nguyên tố lớn hơn 3 nên n ≡ ±1 (mod 6)".

The literal transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L7-FRAG-05.yml`:

  S15    "Vì n là số nguyên tố lớn hơn 3 nên n ≡ ±1 (mod 6)"  -> L7F5_step_S15
  S16    "Giả sử n ≡ −1 (mod 6), suy ra n = 6l−1 … Khi đó, từ
         a^{n(n−2)}+b^{n(n−2)}−c^{n(n−2)} ≡ 0 (mod n²), ta suy ra
         … ⇒ 3a^{n(n−2)} ≡ 0 (mod n²), vô lý"                 -> L7F5_step_S16
  S17    "Vậy n ≡ 1 (mod 6) (đpcm)"                           -> L7F5_step_S17

## Encoding decisions

* S15 is the arithmetic remark: `n` prime > 3 is odd and not divisible by 3,
  so `n % 6 = 1 ∨ n % 6 = 5`.
* S16 is stated with the two facts that `n = 6l−1` supplies and that the
  printed computation actually uses: `n − 2 = 3·k` with `k = 2l−1` odd (the
  print's own substitution `n(n−2) = 3n(2l−1)`), plus `n % 6 = 5`-free
  hypotheses — the reductio proper. The printed intermediate
  "a^{3n(2l−1)} + … ≡ 0 (mod n)" is a weaker reading of the mod-`n²`
  hypothesis it comes from; the substitution that follows uses the mod-`n²`
  forms (19) and (20), which is what is encoded here.
* S17 supplies the missing `k` from `n % 6 = 5` (namely `k = (n−2)/3`) and
  closes the disjunction of S15.
-/

namespace L7

/-- **S15** (author p. 5 §7): "Vì n là số nguyên tố lớn hơn 3 nên n ≡ ±1 (mod 6)"
— for a prime `n > 3`, `n % 6 = 1` or `n % 6 = 5`. -/
theorem L7F5_step_S15 {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n) :
    n % 6 = 1 ∨ n % 6 = 5 := by
  have hodd : n % 2 = 1 := (hn.eq_two_or_odd).resolve_left (by omega)
  have h3ndvd : ¬ 3 ∣ n := by
    intro h
    have hEq : n = 3 := (hn.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp h
    omega
  have h3mod : n % 3 ≠ 0 := fun h => h3ndvd (Nat.dvd_of_mod_eq_zero h)
  omega

/-- **S16** (author p. 5 §7): the printed reductio. Assuming `n ≡ −1 (mod 6)`
(the print's `n = 6l−1`), its substitution `n(n−2) = 3n(2l−1)` is exactly
`n − 2 = 3·k` with `k = 2l−1` odd; then (19), (20) collapse the sum
`a^{n(n−2)}+b^{n(n−2)}−c^{n(n−2)}` to `3·a^{n(n−2)}`, which the mod-`n²`
hypothesis (22') makes `≡ 0`; `n > 3` prime leaves `n ∣ a`, contradicting
`a ⋮̸ n`. -/
theorem L7F5_step_S16 {n k : ℕ} (hn : Nat.Prime n) (h3 : 3 < n) (hk : Odd k)
    (hnk : n - 2 = 3 * k) {a b c : ℤ} (ha : ¬ (n : ℤ) ∣ a)
    (h22 : (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ)
      ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h19 : (c ^ (3 * n) : ℤ) ≡ (-(b ^ (3 * n))) [ZMOD (n ^ 2 : ℤ)])
    (h20 : (a ^ (3 * n) : ℤ) ≡ b ^ (3 * n) [ZMOD (n ^ 2 : ℤ)]) : False := by
  -- the printed exponent identity 3n·k = n(n−2), and the raised powers
  have hexp : 3 * n * k = n * (n - 2) := by rw [hnk]; ring
  have hpow : ∀ x : ℤ, ((x ^ (3 * n)) ^ k : ℤ) = x ^ (n * (n - 2)) := by
    intro x
    rw [← pow_mul, hexp]
  have hb : (b ^ (n * (n - 2)) : ℤ) ≡ a ^ (n * (n - 2)) [ZMOD (n ^ 2 : ℤ)] := by
    have h := h20.pow k
    rw [hpow a, hpow b] at h
    exact h.symm
  have hc : (c ^ (n * (n - 2)) : ℤ) ≡ (-(a ^ (n * (n - 2)))) [ZMOD (n ^ 2 : ℤ)] := by
    have h21 : (c ^ (3 * n) : ℤ) ≡ (-(a ^ (3 * n))) [ZMOD (n ^ 2 : ℤ)] :=
      h19.trans (h20.symm.neg)
    have h := h21.pow k
    have hneg : ((-(a ^ (3 * n)) : ℤ)) ^ k = -((a ^ (3 * n)) ^ k) := Odd.neg_pow hk _
    rw [hneg, hpow a, hpow c] at h
    exact h
  -- the sum collapses to 3·a^{n(n−2)}
  have h1 : (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ)
      ≡ 3 * a ^ (n * (n - 2)) [ZMOD (n ^ 2 : ℤ)] := by
    have h := ((Int.ModEq.refl (a ^ (n * (n - 2)))).add hb).sub hc
    have hid : (a ^ (n * (n - 2)) + a ^ (n * (n - 2)) - (-(a ^ (n * (n - 2)))) : ℤ)
        = 3 * a ^ (n * (n - 2)) := by ring
    rwa [hid] at h
  have hsum : (3 * a ^ (n * (n - 2)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] :=
    h1.symm.trans h22
  -- ⇒ n ∣ a, contradicting `a ⋮̸ n`
  have hdvd : (n : ℤ) ∣ 3 * a ^ (n * (n - 2)) :=
    dvd_trans (dvd_pow_self (n : ℤ) (by norm_num : (2 : ℕ) ≠ 0))
      (Int.modEq_zero_iff_dvd.mp hsum)
  rcases Int.Prime.dvd_mul' hn hdvd with h | h
  · have hle : n ≤ 3 := Nat.le_of_dvd (by norm_num) (Int.natCast_dvd_natCast.mp h)
    omega
  · exact ha (Int.Prime.dvd_pow' hn (k := n * (n - 2)) h)

/-- **S17** (author p. 5 §7): "Vậy n ≡ 1 (mod 6) (đpcm)" — S15's disjunction
with the second case refuted by S16, the `k` of `n − 2 = 3k` being
`(n−2)/3`, which is odd because `n ≡ 5 (mod 6)`. -/
theorem L7F5_step_S17 {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n) {a b c : ℤ}
    (ha : ¬ (n : ℤ) ∣ a)
    (h22 : (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ)
      ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h19 : (c ^ (3 * n) : ℤ) ≡ (-(b ^ (3 * n))) [ZMOD (n ^ 2 : ℤ)])
    (h20 : (a ^ (3 * n) : ℤ) ≡ b ^ (3 * n) [ZMOD (n ^ 2 : ℤ)]) :
    n % 6 = 1 := by
  rcases L7F5_step_S15 hn h3 with h | h
  · exact h
  · exfalso
    have h3dvd : 3 ∣ n - 2 := by
      have hmod : (n - 2) % 3 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨k, hk⟩ := h3dvd
    have hkodd : k % 2 = 1 := by omega
    exact L7F5_step_S16 hn h3 (Nat.odd_iff.mpr hkodd) hk ha h22 h19 h20

end L7
