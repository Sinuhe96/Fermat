/-
Chunk `M1-FRAG-02` — the main proof, p. 6 (`P006-R2`): the printed (7) and (7'),
both read off the expansion of the substituted equation
`(a^n + X)^n + (b^n + X)^n = (h - X)^n`, `X := n^s abck`.

The Vietnamese source text lives in `pipeline/02-chunks/chunks/M1-FRAG-02.yml`.

This file currently carries the *support* lemmas the two labelled steps need.
The pattern is `L6.L6_nsq_dvd_one_add_mul_pow`'s: `add_pow`, then peel the two
surviving terms, then `Finset.dvd_sum` over a tail that vanishes one term at a
time.

Why the support is not optional: (7) is a *congruence of the expansion*, not an
identity. Its whole content is that the tail vanishes — for a prime `n` every
binomial coefficient `C(n,i)` with `1 <= i <= n-1` carries one factor `n`, so a
term carrying `X^i` is divisible by `n^(i*s + 1)`, which is divisible by the
printed modulus as soon as `i >= 2`.
-/
import Mathlib

namespace M1F2

/-- `((x : ZMod M) = 0) ↔ (M : ℤ) ∣ x` — the bridge L5 proves the same way
(`L5.L5_zmod_intCast_eq_zero_iff`). -/
theorem M1F2_zmod_intCast_eq_zero_iff {M : ℕ} [NeZero M] (x : ℤ) :
    ((x : ZMod M) = 0) ↔ (M : ℤ) ∣ x :=
  CharP.intCast_eq_zero_iff (ZMod M) M x

/-- `n^(2s+1) ∣ n^j * Q` whenever `2s+1 ≤ j`: the "the exponent is already big
enough" half of the tail argument. -/
lemma M1F2_pow_dvd_mul {n s j : ℕ} (Q : ℤ) (h : 2 * s + 1 ≤ j) :
    (n : ℤ) ^ (2 * s + 1) ∣ (n : ℤ) ^ j * Q := by
  refine ⟨(n : ℤ) ^ (j - (2 * s + 1)) * Q, ?_⟩
  have h1 : 2 * s + 1 + (j - (2 * s + 1)) = j := Nat.add_sub_of_le h
  rw [← mul_assoc, ← pow_add, h1]

/-- **The vanishing of the tail**, one term: for a prime `n > 11` and `1 ≤ s`,
`n^(2s+1) ∣ C(n,i) * (n^s Q)^i` for every `2 ≤ i ≤ n`.

Two cases, and they are the whole reason the printed modulus is `n^(2s+1)`:
* `i = n`: `C(n,n) = 1`, the term is `n^(sn) Q^n`, and `sn ≥ 2s+1` for `n ≥ 3`;
* `2 ≤ i ≤ n-1`: `n ∣ C(n,i)` (prime `n`), so the term is
  `n^(i*s+1) · (C(n,i)/n) · Q^i`, and `i*s + 1 ≥ 2s+1` for `i ≥ 2`. -/
lemma M1F2_choose_mul_pow_dvd {n s : ℕ} (hn : Nat.Prime n) (hn3 : 3 ≤ n) (hs : 1 ≤ s)
    (Q : ℤ) {i : ℕ} (hi2 : 2 ≤ i) (hin : i ≤ n) :
    (n : ℤ) ^ (2 * s + 1) ∣ (n.choose i : ℤ) * ((n : ℤ) ^ s * Q) ^ i := by
  rcases eq_or_lt_of_le hin with hEq | hLt
  · rw [hEq]
    rw [Nat.choose_self, Nat.cast_one, one_mul, mul_pow, ← pow_mul, mul_comm s n]
    exact M1F2_pow_dvd_mul (Q ^ n) (by
      have h1 : 2 * s + 1 ≤ 3 * s := by omega
      calc 2 * s + 1 ≤ 3 * s := h1
        _ ≤ n * s := Nat.mul_le_mul_right s hn3)
  · obtain ⟨t, ht⟩ := hn.dvd_choose_self (by omega) hLt
    have htZ : (n.choose i : ℤ) = (n : ℤ) * (t : ℤ) := by
      rw [ht, Nat.cast_mul]
    rw [htZ, mul_pow, ← pow_mul]
    have key : (n : ℤ) * (t : ℤ) * ((n : ℤ) ^ (s * i) * Q ^ i)
        = (n : ℤ) ^ (s * i + 1) * ((t : ℤ) * Q ^ i) := by
      rw [pow_succ']
      ring
    rw [key]
    exact M1F2_pow_dvd_mul ((t : ℤ) * Q ^ i) (by
      have h1 : s * 2 ≤ s * i := Nat.mul_le_mul_left s hi2
      omega)

/-- **The truncated expansion** behind the printed (7).

For a prime `n > 11`, `1 ≤ s`, any `y` and `Q`:
`(y + n^s Q)^n = y^n + n y^(n-1) (n^s Q) + T` with `n^(2s+1) ∣ T`.

The `X`-linear coefficient is the print's `n a^{n(n-1)} · n^s abck` at
`y = a^n`; the `h`-side carries `-n h^{n-1}` because `(h - X)^n = (h + (-X))^n`.
This is what (7) is derived from, and the tail `T` is the `Σ_{i≥2}` the print
drops. The split of `range (n+1)` is done on the bound `(n-1)+1+1` rather than
on `n`, so that the rewrites stay inside the sum. -/
lemma M1F2_expand_trunc {n s : ℕ} (hn : Nat.Prime n) (hn3 : 3 ≤ n) (hs : 1 ≤ s)
    (y Q : ℤ) :
    ∃ T : ℤ, (n : ℤ) ^ (2 * s + 1) ∣ T ∧
      (y + (n : ℤ) ^ s * Q) ^ n
        = y ^ n + (n : ℤ) * y ^ (n - 1) * ((n : ℤ) ^ s * Q) + T := by
  refine ⟨∑ m ∈ Finset.range (n - 1),
      y ^ m * ((n : ℤ) ^ s * Q) ^ (n - m) * (n.choose m : ℤ), ?_, ?_⟩
  · refine Finset.dvd_sum fun m hm => ?_
    rw [Finset.mem_range] at hm
    have hi2 : 2 ≤ n - m := by omega
    have hin : n - m ≤ n := by omega
    rw [show y ^ m * ((n : ℤ) ^ s * Q) ^ (n - m) * (n.choose m : ℤ)
        = (n.choose (n - m) : ℤ) * ((n : ℤ) ^ s * Q) ^ (n - m) * y ^ m by
      rw [← Nat.choose_symm (n := n) (k := m) (by omega)]
      ring]
    exact dvd_mul_of_dvd_left (M1F2_choose_mul_pow_dvd hn hn3 hs Q hi2 hin) _
  · have hch : (n.choose (n - 1) : ℤ) = (n : ℤ) := by
      rw [Nat.choose_symm (by omega), Nat.choose_one_right]
    have hn1 : 1 ≤ n := by omega
    have hsplit : (∑ m ∈ Finset.range (n + 1),
          y ^ m * ((n : ℤ) ^ s * Q) ^ (n - m) * (n.choose m : ℤ))
        = (∑ m ∈ Finset.range (n - 1),
            y ^ m * ((n : ℤ) ^ s * Q) ^ (n - m) * (n.choose m : ℤ))
          + y ^ (n - 1) * ((n : ℤ) ^ s * Q) ^ (n - (n - 1)) * (n.choose (n - 1) : ℤ)
          + y ^ n * ((n : ℤ) ^ s * Q) ^ (n - n) * (n.choose n : ℤ) := by
      rw [show n + 1 = (n - 1) + 1 + 1 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ]
      rw [Nat.sub_add_cancel hn1]
    rw [add_pow, hsplit, Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one,
      hch, show n - (n - 1) = 1 by omega, pow_one]
    ring

/-- **S0** — the printed (7) (author p. 6, region `P006-R2`).

"`h^n - a^{n^2} - b^{n^2} ≡ n[a^{n(n-1)} + b^{n(n-1)} + h^{n-1}] n^s abck (mod n^{2s+1})`"

Note the printed `+ h^{n-1}`: the coefficient of `X` in the expansion of the
three `n`-th powers is `n(a^{n(n-1)} + b^{n(n-1)}) + n h^{n-1}`, because
`(h - X)^n` contributes `-(-1)^1 C_n^1 h^{n-1} X = +n h^{n-1} X`. The step is
conditional on the substituted equation (the print's "(3) ⇒"), which is the
hypothesis `hsol` — this is the F1 finding recorded in `M1_LANE.md` §7. -/
theorem M1F2_step_S0_seven {n s : ℕ} {a b c k h : ℤ}
    (hn : Nat.Prime n) (hn3 : 3 ≤ n) (hs : 1 ≤ s)
    (hsol : (a ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
        + (b ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
      = (h - (n : ℤ) ^ s * (a * b * c * k)) ^ n) :
    h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
      ≡ (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
          * ((n : ℤ) ^ s * (a * b * c * k)) [ZMOD (n : ℤ) ^ (2 * s + 1)] := by
  obtain ⟨Ta, hTa, hA⟩ := M1F2_expand_trunc hn hn3 hs (a ^ n) (a * b * c * k)
  obtain ⟨Tb, hTb, hB⟩ := M1F2_expand_trunc hn hn3 hs (b ^ n) (a * b * c * k)
  obtain ⟨Th, hTh, hH⟩ := M1F2_expand_trunc hn hn3 hs h (-(a * b * c * k))
  have hsign : h - (n : ℤ) ^ s * (a * b * c * k)
      = h + (n : ℤ) ^ s * (-(a * b * c * k)) := by ring
  rw [hsign, hA, hB, hH] at hsol
  have hpa : (a ^ n) ^ n = a ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hpb : (b ^ n) ^ n = b ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hpa' : (a ^ n) ^ (n - 1) = a ^ (n * (n - 1)) := by rw [← pow_mul]
  have hpb' : (b ^ n) ^ (n - 1) = b ^ (n * (n - 1)) := by rw [← pow_mul]
  rw [hpa, hpb, hpa', hpb'] at hsol
  have hkey : h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
      = (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
          * ((n : ℤ) ^ s * (a * b * c * k)) + (Ta + Tb - Th) := by
    linarith [hsol]
  have hdiv : (n : ℤ) ^ (2 * s + 1) ∣ Ta + Tb - Th :=
    dvd_add (dvd_add hTa hTb) (dvd_neg.mpr hTh)
  have hfin : (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
        * ((n : ℤ) ^ s * (a * b * c * k)) - (h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2))
      = -(Ta + Tb - Th) := by
    linarith [hkey]
  rw [Int.modEq_iff_dvd, hfin]
  exact dvd_neg.mpr hdiv

/-- **S1** — the printed (7′) (author p. 6, region `P006-R2`), which the print
places at the end of display (9)'s line.

"`h^n ≡ a^{n^2} + b^{n^2} (mod n^{s+1})`".

It is a one-line consequence of (7) and not an independent claim: (7)'s
right-hand side is `n[...] · n^s abck`, i.e. `n^{s+1}` times an integer, so it is
`≡ 0 (mod n^{s+1})`, and (7) read mod `n^{s+1}` (which follows from (7) mod
`n^{2s+1}`, since `s+1 ≤ 2s+1` for `s ≥ 0`) gives exactly this. The print labels
it, so it is a separate step here. -/
theorem M1F2_step_S1_seven_prime {n s : ℕ} {a b c k h : ℤ} (hs : 0 ≤ s)
    (h7 : h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
      ≡ (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
          * ((n : ℤ) ^ s * (a * b * c * k)) [ZMOD (n : ℤ) ^ (2 * s + 1)]) :
    h ^ n ≡ a ^ (n ^ 2) + b ^ (n ^ 2) [ZMOD (n : ℤ) ^ (s + 1)] := by
  have hdvd : (n : ℤ) ^ (s + 1) ∣
      (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
        * ((n : ℤ) ^ s * (a * b * c * k)) := by
    refine ⟨(a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1)) * (a * b * c * k), ?_⟩
    rw [pow_succ]
    ring
  have hmod : (n : ℤ) ^ (s + 1) ∣ (n : ℤ) ^ (2 * s + 1) := by
    refine ⟨(n : ℤ) ^ (2 * s + 1 - (s + 1)), ?_⟩
    rw [← pow_add, Nat.add_sub_of_le (by omega)]
  have h0 : h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2) ≡ 0 [ZMOD (n : ℤ) ^ (s + 1)] :=
    (h7.of_dvd hmod).trans (Int.modEq_zero_iff_dvd.mpr hdvd)
  have hfin : a ^ (n ^ 2) + b ^ (n ^ 2) - h ^ n
      = -(h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)) := by ring
  rw [Int.modEq_iff_dvd, hfin]
  exact dvd_neg.mpr (Int.modEq_zero_iff_dvd.mp h0)

end M1F2

-- DONE-flip evidence: permitted axioms only, and no `sorryAx`.
#print axioms M1F2.M1F2_step_S0_seven
#print axioms M1F2.M1F2_step_S1_seven_prime
