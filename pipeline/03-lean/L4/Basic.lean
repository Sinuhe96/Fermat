import Mathlib
import L3.Basic

/-!
# Lemma 4 (bổ đề 4) — the author's proof, steps S0–S7

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 1, lemma 4 of section A;
  * proof: p. 2, section "4. Chứng minh bổ đề 4".

The literal Vietnamese transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L4-01.yml` (`source_text`, `author_steps`).
One named declaration per author step (English paraphrase):

  S0     hypotheses: n ∈ ℕ positive odd; a,b,c,m ∈ ℤ*; |a|,|b|,|c| ≥ 2;
         m prime; (a,b) = m; a·b = c^n; b ⋮̸ m²      -> carried by the step theorems
  S1+S2  m | a and m | b follow from (a,b) = m; with a·b = c^n this gives
         m² | c^n, hence c ⋮ m because m is prime   -> L4_step_S1_S2
  S3     c = m^s·r with m ∤ r (the m-adic decomposition of c), n·s ≥ 2

                                                    -> L4_step_S3
  S4     b = m·h and a = m^k·l with k ≥ 1, (h,l) = 1, m ∤ h, m ∤ l

                                                    -> L4_step_S4
  S5     m^{k+1}·h·l = m^{ns}·r^n forces k+1 = n·s and h·l = r^n

                                                    -> L4_step_S5
  S6     bổ đề 3 on h·l = r^n (n odd, (h,l) = 1) gives r = c₁·c₂, h = c₁^n,
         l = c₂^n                                   -> L4_step_S6
  S7     assemble: c = m^s·c₁·c₂, a = m^{ns−1}·c₂^n, b = m·c₁^n

                                                    -> L4_bo_de_4

S6 cites bổ đề 3 and therefore *imports* the verified module `L3.Basic`
(ENCODING_MAP §A "Reusing a DONE chunk") rather than restating or reproving it.

Nothing here is our own mathematics: the content is the author's chain.
-/

namespace L4

/-- **S1+S2** (author p. 2 §4, first paragraph).

From `(a,b) = m` the prime `m` divides both `a` and `b`; hence `m²` divides
`a·b`, which is `c^n` by hypothesis, so `c^n ⋮ m²`. Because `m` is prime,
`m² ∣ c^n` forces `m ∣ c` (the author's parenthetical "do `m` là số nguyên tố").

`hm` is the author's hypothesis that `m` is prime; it does the work only in
the second conjunct. -/
theorem L4_step_S1_S2 {a b c : ℤ} {m n : ℕ} (hm : Nat.Prime m)
    (hgcd : Int.gcd a b = m) (hab : a * b = c ^ n) :
    (m : ℤ) ^ 2 ∣ c ^ n ∧ (m : ℤ) ∣ c := by
  have hma : (m : ℤ) ∣ a := by
    simpa [hgcd] using Int.gcd_dvd_left a b
  have hmb : (m : ℤ) ∣ b := by
    simpa [hgcd] using Int.gcd_dvd_right a b
  have hsq : (m : ℤ) ^ 2 ∣ c ^ n := by
    have h2 : (m : ℤ) * (m : ℤ) ∣ a * b := mul_dvd_mul hma hmb
    rw [hab, ← pow_two] at h2
    exact h2
  have hmm : (m : ℤ) ∣ (m : ℤ) ^ 2 := ⟨(m : ℤ), by rw [pow_two]⟩
  exact ⟨hsq, Int.Prime.dvd_pow' (p := m) (n := c) (k := n) hm (dvd_trans hmm hsq)⟩

/-- **S3** (author p. 2 §4, first paragraph, second sentence).

`c` has an m-adic decomposition `c = m^s·r` with `m ∤ r` (well defined
because `m ∣ c`, from S1+S2, and `m` is prime): take `s` maximal. Because
`c^n = m^{ns}·r^n` is then divisible by `m²` (S1+S2) while `m ∤ r`, the
exponent must satisfy `n·s ≥ 2` (the author's "nên `ns ≥ 2`").

The decomposition is computed on `c.natAbs` (`Nat.exists_eq_pow_mul_and_not_dvd`,
the m-adic decomposition of a natural number) and transported to `ℤ` by
dividing `c` by `m^s`; maximality of `s` is what gives `m ∤ r`. -/
theorem L4_step_S3 {c : ℤ} {m n : ℕ} (hm : Nat.Prime m)
    (hmc : (m : ℤ) ∣ c) (hc : c ≠ 0) (hsq : (m : ℤ) ^ 2 ∣ c ^ n) :
    ∃ s : ℕ, ∃ r : ℤ, 1 ≤ s ∧ r ≠ 0 ∧ ¬(m : ℤ) ∣ r ∧
      c = (m : ℤ) ^ s * r ∧ 2 ≤ n * s := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hC0 : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  obtain ⟨s, R, hR, hCR⟩ := Nat.exists_eq_pow_mul_and_not_dvd hC0 m hm.ne_one
  have hmC : m ∣ c.natAbs := Int.natCast_dvd.mp hmc
  have hR0 : R ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hCR
    exact hC0 hCR
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exfalso
      rw [h, pow_zero, one_mul] at hCR
      exact hR (hCR ▸ hmC)
    · exact h
  have hmdvd : (m : ℤ) ^ s ∣ c := by
    have h1 : ((m ^ s : ℕ) : ℤ) ∣ c := Int.natCast_dvd.mpr ⟨R, hCR⟩
    simpa only [Nat.cast_pow] using h1
  obtain ⟨r, hr⟩ := hmdvd
  have hr_ne : r ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hr
    exact hc hr
  have hrnat : r.natAbs = R := by
    have h := congrArg Int.natAbs hr
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h
    rw [hCR] at h
    exact (mul_left_cancel₀ (pow_ne_zero s hm0) h).symm
  have hr_not : ¬(m : ℤ) ∣ r := by
    rintro h
    exact hR (by rw [← hrnat]; exact Int.natCast_dvd.mp h)
  have h2 : 2 ≤ n * s := by
    have hdvd : m ^ 2 ∣ c.natAbs ^ n := by
      have h := (Int.natAbs_dvd_natAbs (a := (m : ℤ) ^ 2) (b := c ^ n)).mpr hsq
      simpa only [Int.natAbs_pow, Int.natAbs_natCast] using h
    rw [hCR] at hdvd
    have hcop : Nat.Coprime (m ^ 2) (R ^ n) :=
      ((hm.coprime_iff_not_dvd).mpr hR).pow 2 n
    have hM : m ^ 2 ∣ (m ^ s) ^ n := by
      rw [mul_pow] at hdvd
      exact hcop.dvd_of_dvd_mul_right hdvd
    rw [← pow_mul] at hM
    have hle : 2 ≤ s * n := (Nat.pow_dvd_pow_iff_le_right hm.one_lt).mp hM
    simpa only [mul_comm] using hle
  exact ⟨s, r, hs1, hr_ne, hr_not, hr, h2⟩

/-- **S4** (author p. 2 §4, second paragraph).

`(a,b) = m` together with `b ⋮̸ m²` gives the m-adic split of the pair:
`b = m·h` with `m ∤ h` (the author's `b ⋮̸ m²` is exactly what forbids a
second factor of `m` in `b`), and `a = m^k·l` with `k ≥ 1` and `m ∤ l`.

The coprimality `(h,l) = 1` comes from `(a,b) = m`: a common divisor `d` of
`h` and `l` makes `m·d` a common divisor of `b = m·h` and `a = m^k·l`, hence
`m·d ∣ (a,b) = m`, so `d = 1`.

`ha`/`hb` are the author's `a,b ∈ ℤ*`; they are what make `h` and `l` nonzero. -/
theorem L4_step_S4 {a b : ℤ} {m : ℕ} (hm : Nat.Prime m) (ha : a ≠ 0) (hb : b ≠ 0)
    (hgcd : Int.gcd a b = m) (hb2 : ¬(m : ℤ) ^ 2 ∣ b) :
    ∃ k : ℕ, ∃ h l : ℤ, 1 ≤ k ∧ h ≠ 0 ∧ l ≠ 0 ∧ Int.gcd h l = 1 ∧
      ¬(m : ℤ) ∣ h ∧ ¬(m : ℤ) ∣ l ∧ b = (m : ℤ) * h ∧ a = (m : ℤ) ^ k * l := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hm2 : 2 ≤ m := hm.two_le
  have hma : (m : ℤ) ∣ a := by simpa [hgcd] using Int.gcd_dvd_left a b
  have hmb : (m : ℤ) ∣ b := by simpa [hgcd] using Int.gcd_dvd_right a b
  obtain ⟨h, hh⟩ := hmb
  have hh_ne : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hh
    exact hb hh
  have hmh : ¬(m : ℤ) ∣ h := by
    rintro ⟨h', hh'⟩
    exact hb2 ⟨h', by rw [hh, hh', pow_two]; ring⟩
  have hA0 : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  obtain ⟨k, L, hL, hAL⟩ := Nat.exists_eq_pow_mul_and_not_dvd hA0 m hm.ne_one
  have hmA : m ∣ a.natAbs := Int.natCast_dvd.mp hma
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      rw [h, pow_zero, one_mul] at hAL
      exact hL (hAL ▸ hmA)
    · exact h
  have hmdvd : (m : ℤ) ^ k ∣ a := by
    have h1 : ((m ^ k : ℕ) : ℤ) ∣ a := Int.natCast_dvd.mpr ⟨L, hAL⟩
    simpa only [Nat.cast_pow] using h1
  obtain ⟨l, hl⟩ := hmdvd
  have hl_ne : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hl
    exact ha hl
  have hlnat : l.natAbs = L := by
    have h := congrArg Int.natAbs hl
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h
    rw [hAL] at h
    exact (mul_left_cancel₀ (pow_ne_zero k hm0) h).symm
  have hl_not : ¬(m : ℤ) ∣ l := by
    rintro h
    exact hL (by rw [← hlnat]; exact Int.natCast_dvd.mp h)
  have hcop : Int.gcd h l = 1 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    obtain ⟨h', hh'⟩ := Int.gcd_dvd_left h l
    obtain ⟨l', hl'⟩ := Int.gcd_dvd_right h l
    have hda : ((m * Int.gcd h l : ℕ) : ℤ) ∣ a := by
      refine ⟨(m : ℤ) ^ j * l', ?_⟩
      calc a = (m : ℤ) ^ k * l := hl
        _ = (m : ℤ) ^ (j + 1) * l := by rw [hj]
        _ = (m : ℤ) * (m : ℤ) ^ j * l := by rw [pow_succ']
        _ = (m : ℤ) * (m : ℤ) ^ j * ((Int.gcd h l : ℤ) * l') := by
              conv_lhs => rw [hl']
        _ = ((m * Int.gcd h l : ℕ) : ℤ) * ((m : ℤ) ^ j * l') := by
              push_cast; ring
    have hdb : ((m * Int.gcd h l : ℕ) : ℤ) ∣ b := by
      refine ⟨h', ?_⟩
      calc b = (m : ℤ) * h := hh
        _ = (m : ℤ) * ((Int.gcd h l : ℤ) * h') := by
              conv_lhs => rw [hh']
        _ = ((m * Int.gcd h l : ℕ) : ℤ) * h' := by push_cast; ring
    have hdiv : m * Int.gcd h l ∣ m := by
      have h := Int.dvd_gcd hda hdb
      rwa [hgcd] at h
    exact Nat.dvd_one.mp
      (Nat.dvd_of_mul_dvd_mul_left (k := m) (by omega : 0 < m) (by simpa using hdiv))
  exact ⟨k, h, l, hk1, hh_ne, hl_ne, hcop, hmh, hl_not, hh, hl⟩

/-- **S5** (author p. 2 §4, third paragraph).

Substituting the decompositions of S3 and S4 into `a·b = c^n` gives

  `m^{k+1}·(h·l) = m^{n·s}·r^n`.

Since `m` is prime and `m ∤ h`, `m ∤ l`, `m ∤ r`, both sides have the same
m-adic valuation at `m`, so the exponents must agree: `k+1 = n·s` (the
author's "suy ra `k+1 = ns`"), and cancelling `m^{k+1}` gives `h·l = r^n`.

The valuations are read off with `Nat.factorization` on `natAbs`: for a
prime `m` and `m ∤ X`, `(m^a * X).factorization m = a`. -/
theorem L4_step_S5 {a b c : ℤ} {m n : ℕ} (hm : Nat.Prime m)
    {k s : ℕ} {h l r : ℤ}
    (hh : ¬(m : ℤ) ∣ h) (hl : ¬(m : ℤ) ∣ l) (hr : ¬(m : ℤ) ∣ r)
    (hab : a * b = c ^ n) (ha : a = (m : ℤ) ^ k * l) (hb : b = (m : ℤ) * h)
    (hc : c = (m : ℤ) ^ s * r) :
    k + 1 = n * s ∧ h * l = r ^ n := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hh0 : h ≠ 0 := fun h0 => hh (by rw [h0]; exact dvd_zero _)
  have hl0 : l ≠ 0 := fun h0 => hl (by rw [h0]; exact dvd_zero _)
  have hr0 : r ≠ 0 := fun h0 => hr (by rw [h0]; exact dvd_zero _)
  have hne : (h * l).natAbs ≠ 0 := by
    rw [Int.natAbs_mul]
    exact mul_ne_zero (Int.natAbs_ne_zero.mpr hh0) (Int.natAbs_ne_zero.mpr hl0)
  have hnotdvd : ¬ m ∣ (h * l).natAbs := by
    intro hd
    exact (Int.Prime.dvd_mul' hm (Int.natCast_dvd.mpr hd)).elim hh hl
  have hrnotdvd : ¬ m ∣ r.natAbs ^ n := by
    intro hd
    have h2 : ((m : ℤ).natAbs) ∣ (r ^ n).natAbs := by
      simpa only [Int.natAbs_pow, Int.natAbs_natCast] using hd
    exact hr (Int.Prime.dvd_pow' (p := m) (n := r) (k := n) hm
      ((Int.natAbs_dvd_natAbs (a := (m : ℤ)) (b := r ^ n)).mp h2))
  -- the substituted equation, m^(k+1)·(h·l) = m^(n·s)·r^n
  have E : (m : ℤ) ^ (k + 1) * (h * l) = (m : ℤ) ^ (n * s) * r ^ n := by
    have hab' : ((m : ℤ) ^ k * l) * ((m : ℤ) * h) = c ^ n := by
      rw [← ha, ← hb]; exact hab
    have hc' : c ^ n = (m : ℤ) ^ (s * n) * r ^ n := by rw [hc, mul_pow, ← pow_mul]
    calc (m : ℤ) ^ (k + 1) * (h * l)
        = ((m : ℤ) ^ k * (m : ℤ)) * (l * h) := by rw [pow_succ]; ring
      _ = ((m : ℤ) ^ k * l) * ((m : ℤ) * h) := by ring
      _ = c ^ n := hab'
      _ = (m : ℤ) ^ (s * n) * r ^ n := hc'
      _ = (m : ℤ) ^ (n * s) * r ^ n := by rw [mul_comm s n]
  -- m-adic valuations: (m^a * X).factorization m = a when m ∤ X
  have key : ∀ a X : ℕ, X ≠ 0 → ¬m ∣ X → (m ^ a * X).factorization m = a := by
    intro a X hX0 hX
    rw [Nat.factorization_mul (pow_ne_zero a hm0) hX0, Finsupp.add_apply,
      Nat.factorization_pow_self hm, Nat.factorization_eq_zero_of_not_dvd hX, add_zero]
  have hL : (m ^ (k + 1) * (h * l).natAbs).factorization m = k + 1 :=
    key (k + 1) _ hne hnotdvd
  have hR : (m ^ (n * s) * r.natAbs ^ n).factorization m = n * s :=
    key (n * s) _ (pow_ne_zero n (Int.natAbs_ne_zero.mpr hr0)) hrnotdvd
  have hnat : m ^ (k + 1) * (h * l).natAbs = m ^ (n * s) * r.natAbs ^ n := by
    have h := congrArg Int.natAbs E
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using h
  have hks : k + 1 = n * s := by rw [← hL, ← hR, hnat]
  refine ⟨hks, ?_⟩
  have hcancel : (m : ℤ) ^ (k + 1) * (h * l) = (m : ℤ) ^ (k + 1) * r ^ n := by
    rw [E, hks]
  exact mul_left_cancel₀ (pow_ne_zero (k + 1) (by exact_mod_cast hm0)) hcancel

/-- **S6** (author p. 2 §4, third paragraph, final clause).

`h·l = r^n` with `n` odd and `(h,l) = 1` is exactly bổ đề 3, applied with
`a := h`, `b := l`, `c := r`. This is the citation point: the proof is the
*imported* `L3.L3_bo_de_3` (see `import L3.Basic`), not a restatement of it,
so the thing this chunk relies on is the thing L3-01 verified. -/
theorem L4_step_S6 {h l r : ℤ} {n : ℕ} (h0 : h ≠ 0) (l0 : l ≠ 0) (r0 : r ≠ 0)
    (hn : Odd n) (hn0 : 0 < n) (hgcd : Int.gcd h l = 1) (hhl : h * l = r ^ n) :
    ∃ c1 c2 : ℤ, c1 ≠ 0 ∧ c2 ≠ 0 ∧ Int.gcd c1 c2 = 1 ∧
      r = c1 * c2 ∧ h = c1 ^ n ∧ l = c2 ^ n :=
  L3.L3_bo_de_3 hn hn0 h0 l0 r0 hhl hgcd

/-- **S7 / assembly** — bổ đề 4 (author p. 2 §4, closing "Bổ đề 4 đã được
chứng minh.").

Chains S1+S2, S3, S4, S5, S6 in the author's order, ending on S6's witnesses
`c₁, c₂`; `k = n·s − 1` comes from S5's `k+1 = n·s`.

`_ha2`/`_hb2`/`_hc2` carry the author's `|a|, |b|, |c| ≥ 2` for
faithfulness — no step of his proof consumes them. -/
theorem L4_bo_de_4 {a b c : ℤ} {m n : ℕ} (hm : Nat.Prime m) (hn : Odd n)
    (hn0 : 0 < n) (_ha2 : 2 ≤ a.natAbs) (_hb2 : 2 ≤ b.natAbs)
    (_hc2 : 2 ≤ c.natAbs) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a * b = c ^ n) (hgcd : Int.gcd a b = m) (hb2 : ¬(m : ℤ) ^ 2 ∣ b) :
    ∃ s : ℕ, ∃ c1 c2 : ℤ, 1 ≤ s ∧ 2 ≤ n * s ∧ c1 ≠ 0 ∧ c2 ≠ 0 ∧
      Int.gcd c1 c2 = 1 ∧ ¬(m : ℤ) ∣ c1 ∧ ¬(m : ℤ) ∣ c2 ∧
      c = (m : ℤ) ^ s * (c1 * c2) ∧ a = (m : ℤ) ^ (n * s - 1) * c2 ^ n ∧
      b = (m : ℤ) * c1 ^ n := by
  obtain ⟨hsq, hmc⟩ := L4_step_S1_S2 hm hgcd hab
  obtain ⟨s, r, hs1, hr_ne, hr_not, hc_eq, hns⟩ := L4_step_S3 hm hmc hc hsq
  obtain ⟨k, h, l, _, hh_ne, hl_ne, hgcd_hl, hmh, hml, hb_eq, ha_eq⟩ :=
    L4_step_S4 hm ha hb hgcd hb2
  obtain ⟨hks, hhl⟩ := L4_step_S5 hm hmh hml hr_not hab ha_eq hb_eq hc_eq
  obtain ⟨c1, c2, hc1_ne, hc2_ne, hgcd12, hr_eq, hh_eq, hl_eq⟩ :=
    L4_step_S6 hh_ne hl_ne hr_ne hn hn0 hgcd_hl hhl
  have hmc1 : ¬(m : ℤ) ∣ c1 := by
    intro hd
    exact hmh (by rw [hh_eq]; exact dvd_pow hd (by omega : n ≠ 0))
  have hmc2 : ¬(m : ℤ) ∣ c2 := by
    intro hd
    exact hml (by rw [hl_eq]; exact dvd_pow hd (by omega : n ≠ 0))
  refine ⟨s, c1, c2, hs1, hns, hc1_ne, hc2_ne, hgcd12, hmc1, hmc2, ?_, ?_, ?_⟩
  · rw [hc_eq, hr_eq]
  · rw [ha_eq, hl_eq, show k = n * s - 1 by omega]
  · rw [hb_eq, hh_eq]

#print axioms L4.L4_step_S1_S2
#print axioms L4.L4_step_S3
#print axioms L4.L4_step_S4
#print axioms L4.L4_step_S5
#print axioms L4.L4_step_S6
#print axioms L4.L4_bo_de_4

end L4
