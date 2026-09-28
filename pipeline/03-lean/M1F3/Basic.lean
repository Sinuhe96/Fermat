/-
Chunk `M1-FRAG-03` — the main proof, p. 6 (`P006-R2`): the printed **(8)**, **(9)**
and **(10)**.

These are the same expansion as the printed (7) (chunk `M1-FRAG-02`) at higher
orders, so this file reuses `M1F2.M1F2_choose_mul_pow_dvd` — the lemma that a
prime `n` divides `C(n,i)` for `1 ≤ i ≤ n-1`, which is the *whole* reason the
printed moduli are `n^{3s+1}`, `n^{4s+1}`, `n^{5s+1}` — and generalizes `M1F2`'s
two-term truncation to any order `r`.

The three printed claims, kept in the author's order:

  (8)  h^n - a^{n^2} - b^{n^2} ≡ (i = 1, 2 terms)   (mod n^{3s+1})
  (9)  h^n - a^{n^2} - b^{n^2} ≡ (i = 1, 2, 3 terms) (mod n^{4s+1})
  (10) h^n - a^{n^2} - b^{n^2} - (i = 1 term) ≡ (i = 2, 3, 4 terms) (mod n^{5s+1})

with, from the expansion of `(a^n + X)^n + (b^n + X)^n - (h - X)^n = 0`
(`X := n^s abck`), the i-th combined term being

  C(n,i) · [a^{n(n-i)} + b^{n(n-i)} + (-1)^{i+1} h^{n-i}] · X^i

— the `(-1)^{i+1}` is why the printed brackets alternate
`[a^{n(n-1)} + b^{n(n-1)} + h^{n-1}]`, `[b^{n(n-2)} + a^{n(n-2)} - h^{n-2}]`,
`[b^{n(n-3)} + a^{n(n-3)} + h^{n-3}]`,
`[b^{n(n-4)} + a^{n(n-4)} - h^{n-4}]`; the published `n(n-1)/2`, `n(n-1)(n-2)/6`,
`n(n-1)(n-2)(n-3)/24` are `n.choose 2`, `n.choose 3`, `n.choose 4`, which is the
form used here (no division, and faithful — those fractions *are* the binomial
coefficients).

Each step is conditional on the substituted equation, i.e. on (3) read through
the author's substitution — the same F1 finding as `M1-FRAG-02`, so the equation
is a hypothesis here, never an axiom.
-/
import Mathlib

-- Deliberately no `import M1F2.Basic`: this leaf's tail lemma needs a two-case
-- argument of its own (see `M1F3_tail_dvd`), because `M1F2_choose_mul_pow_dvd`
-- only extracts `n^(2s+1)` and throws away the extra `n^((j-2)s)` that the
-- higher printed moduli need. M1F2 remains the *pattern*; nothing is imported
-- from it, so this chunk depends on no other Lean module.

namespace M1F3

/-- The binomial expansion indexed by the **power of `X`** rather than by the
power of `y`: `(y + X)^n = Σ_i C(n,i) y^{n-i} X^i`.

`add_pow` gives the `y`-indexed form; `Finset.sum_range_reflect` reverses the
index and `Nat.choose_symm` turns `C(n, n-i)` into `C(n,i)`. Needed because the
print keeps *low powers of `X`* (`X` is `n^s abck`, the small parameter), so the
tail to be shown divisible is the top of the `y`-index range. -/
lemma M1F3_add_pow_index (y X : ℤ) (n : ℕ) :
    (y + X) ^ n
      = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) * y ^ (n - i) * X ^ i := by
  rw [add_pow]
  rw [← Finset.sum_range_reflect
    (f := fun m => y ^ m * X ^ (n - m) * (n.choose m : ℤ)) (n := n + 1)]
  rw [show n + 1 - 1 = n by omega]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [Finset.mem_range] at hm
  have hmle : m ≤ n := by omega
  rw [Nat.choose_symm hmle]
  have h1 : n - (n - m) = m := by omega
  rw [h1]
  ring

/-- **The tail's divisibility at order `r`** — the reason the printed moduli are
`n^{(r+1)s+1}`.

Every term of the tail carries `X^j` with `j ≥ r+1`, and `n^((r+1)s+1)` divides
`C(n,j) · X^j`:

* `j = n`: `C(n,n) = 1`, the term is `n^{sn} Q^n`, and `sn ≥ (r+1)s + 1`
  because `n ≥ r+2` and `s ≥ 1`;
* `r+1 ≤ j < n`: the prime `n` divides `C(n,j)`, so the term is
  `n^{js+1} · (C(n,j)/n) · Q^j`, and `js + 1 ≥ (r+1)s + 1` since `j ≥ r+1`.

This is *not* `M1F2_choose_mul_pow_dvd` plus exponent monotonicity: that lemma
concludes only `n^(2s+1) ∣ …`, and a larger power is not recoverable from it
(the leftover `n^((j-2)s)` is not tracked). Hence the separate lemma. -/
lemma M1F3_tail_dvd {n s r : ℕ} (hn : Nat.Prime n) (_hn3 : 3 ≤ n) (hs : 1 ≤ s)
    (hrn : r + 2 ≤ n) (Q : ℤ) {j : ℕ} (hrj : r + 1 ≤ j) (hjn : j ≤ n) :
    (n : ℤ) ^ ((r + 1) * s + 1) ∣ (n.choose j : ℤ) * ((n : ℤ) ^ s * Q) ^ j := by
  rcases eq_or_lt_of_le hjn with hEq | hLt
  · rw [hEq, Nat.choose_self, Nat.cast_one, one_mul, mul_pow, ← pow_mul, mul_comm s n]
    refine dvd_mul_of_dvd_left (pow_dvd_pow (n : ℤ) ?_) _
    have hstep : (r + 1) * s + 1 ≤ (r + 2) * s := by
      rw [show (r + 2) * s = (r + 1) * s + s by ring]
      omega
    exact le_trans hstep (Nat.mul_le_mul_right s hrn)
  · obtain ⟨t, ht⟩ := hn.dvd_choose_self (by omega) hLt
    have htZ : (n.choose j : ℤ) = (n : ℤ) * (t : ℤ) := by rw [ht, Nat.cast_mul]
    rw [htZ, mul_pow, ← pow_mul]
    have key : (n : ℤ) * (t : ℤ) * ((n : ℤ) ^ (s * j) * Q ^ j)
        = (n : ℤ) ^ (s * j + 1) * ((t : ℤ) * Q ^ j) := by
      rw [pow_succ']
      ring
    rw [key]
    refine dvd_mul_of_dvd_left (pow_dvd_pow (n : ℤ) ?_) _
    have h6 : (r + 1) * s ≤ s * j := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right s hrj
    exact Nat.add_le_add_right h6 1

/-- **The r-th order truncation** the printed (8), (9), (10) all rest on.

For a prime `n > 11`, `1 ≤ s ≤ r ≤ n`, any `y, Q`:
`(y + n^s Q)^n = Σ_{i≤r} C(n,i) y^{n-i} (n^s Q)^i + T` with
`n^{(r+1)s+1} ∣ T`.

Every term of the tail carries `X^i` with `i ≥ r+1`, and `C(n,i)` contributes a
factor `n` (`M1F2_choose_mul_pow_dvd`), so it is divisible by
`n^{i s + 1} ≥ n^{(r+1)s+1}`. This is `M1F2.M1F2_expand_trunc` (which is the
case `r = 1`) at general `r`. -/
lemma M1F3_expand_trunc {n s r : ℕ} (hn : Nat.Prime n) (hn3 : 3 ≤ n) (hs : 1 ≤ s)
    (hrn : r + 2 ≤ n) (y Q : ℤ) :
    ∃ T : ℤ, (n : ℤ) ^ ((r + 1) * s + 1) ∣ T ∧
      (y + (n : ℤ) ^ s * Q) ^ n
        = (∑ i ∈ Finset.range (r + 1),
            (n.choose i : ℤ) * y ^ (n - i) * ((n : ℤ) ^ s * Q) ^ i) + T := by
  refine ⟨∑ i ∈ Finset.range (n - r),
      (n.choose (r + 1 + i) : ℤ) * y ^ (n - (r + 1 + i))
        * ((n : ℤ) ^ s * Q) ^ (r + 1 + i), ?_, ?_⟩
  · refine Finset.dvd_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hd := M1F3_tail_dvd hn hn3 hs hrn Q (j := r + 1 + i) (by omega) (by omega)
    have hrw : (n.choose (r + 1 + i) : ℤ) * y ^ (n - (r + 1 + i))
          * ((n : ℤ) ^ s * Q) ^ (r + 1 + i)
        = ((n.choose (r + 1 + i) : ℤ) * ((n : ℤ) ^ s * Q) ^ (r + 1 + i))
          * y ^ (n - (r + 1 + i)) := by
      ring
    rw [hrw]
    exact dvd_mul_of_dvd_left hd _
  · rw [M1F3_add_pow_index y ((n : ℤ) ^ s * Q) n]
    rw [show n + 1 = (r + 1) + (n - r) by omega]
    rw [Finset.sum_range_add]

/-- **S0** — the printed (8) (author p. 6, region `P006-R2`):

"`h^n - a^{n^2} - b^{n^2} ≡ n[a^{n(n-1)} + b^{n(n-1)} + h^{n-1}] n^s abck
+ (n(n-1)/2)[b^{n(n-2)} + a^{n(n-2)} - h^{n-2}](n^s abck)^2 (mod n^{3s+1})`"

This is `M1F3_expand_trunc` at `r = 2` applied to the three `n`-th powers of the
substituted equation. Note the printed order inside the order-2 bracket is
`b` then `a` (the order-1 bracket has `a` first); both are used as printed. -/
theorem M1F3_step_S0_eight {n s : ℕ} {a b c k h : ℤ}
    (hn : Nat.Prime n) (hn11 : 11 < n) (hs : 1 ≤ s)
    (hsol : (a ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
        + (b ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
      = (h - (n : ℤ) ^ s * (a * b * c * k)) ^ n) :
    h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
      ≡ (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
            * ((n : ℤ) ^ s * (a * b * c * k))
        + (n.choose 2 : ℤ) * (b ^ (n * (n - 2)) + a ^ (n * (n - 2)) - h ^ (n - 2))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 2
        [ZMOD (n : ℤ) ^ (3 * s + 1)] := by
  obtain ⟨Ta, hTa, hA⟩ :=
    M1F3_expand_trunc hn (by omega) hs (r := 2) (by omega) (a ^ n) (a * b * c * k)
  obtain ⟨Tb, hTb, hB⟩ :=
    M1F3_expand_trunc hn (by omega) hs (r := 2) (by omega) (b ^ n) (a * b * c * k)
  obtain ⟨Th, hTh, hH⟩ :=
    M1F3_expand_trunc hn (by omega) hs (r := 2) (by omega) h (-(a * b * c * k))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    Nat.sub_zero, pow_zero, pow_one, mul_one, zero_add] at hA hB hH
  have hsign : h - (n : ℤ) ^ s * (a * b * c * k)
      = h + (n : ℤ) ^ s * (-(a * b * c * k)) := by ring
  rw [hsign] at hsol
  have hpa : (a ^ n) ^ n = a ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hpb : (b ^ n) ^ n = b ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hpa' : (a ^ n) ^ (n - 1) = a ^ (n * (n - 1)) := by rw [← pow_mul]
  have hpb' : (b ^ n) ^ (n - 1) = b ^ (n * (n - 1)) := by rw [← pow_mul]
  have hpa'' : (a ^ n) ^ (n - 2) = a ^ (n * (n - 2)) := by rw [← pow_mul]
  have hpb'' : (b ^ n) ^ (n - 2) = b ^ (n * (n - 2)) := by rw [← pow_mul]
  rw [hpa, hpa', hpa''] at hA
  rw [hpb, hpb', hpb''] at hB
  have hkey : h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
      = (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
            * ((n : ℤ) ^ s * (a * b * c * k))
        + (n.choose 2 : ℤ) * (b ^ (n * (n - 2)) + a ^ (n * (n - 2)) - h ^ (n - 2))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 2
        + (Ta + Tb - Th) := by
    linarith [hA, hB, hH, hsol]
  have hdiv : (n : ℤ) ^ (3 * s + 1) ∣ Ta + Tb - Th :=
    dvd_add (dvd_add hTa hTb) (dvd_neg.mpr hTh)
  have hfin : (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
            * ((n : ℤ) ^ s * (a * b * c * k))
        + (n.choose 2 : ℤ) * (b ^ (n * (n - 2)) + a ^ (n * (n - 2)) - h ^ (n - 2))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 2
        - (h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2))
      = -(Ta + Tb - Th) := by
    linarith [hkey]
  rw [Int.modEq_iff_dvd, hfin]
  exact dvd_neg.mpr hdiv

/-- **S1** — the printed (9) (author p. 6, region `P006-R2`): the same congruence
one order higher, `(mod n^{4s+1})`, adding the `C(n,3)` term with the printed
`[b^{n(n-3)} + a^{n(n-3)} + h^{n-3}]`. -/
theorem M1F3_step_S1_nine {n s : ℕ} {a b c k h : ℤ}
    (hn : Nat.Prime n) (hn11 : 11 < n) (hs : 1 ≤ s)
    (hsol : (a ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
        + (b ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
      = (h - (n : ℤ) ^ s * (a * b * c * k)) ^ n) :
    h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
      ≡ (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
            * ((n : ℤ) ^ s * (a * b * c * k))
        + (n.choose 2 : ℤ) * (b ^ (n * (n - 2)) + a ^ (n * (n - 2)) - h ^ (n - 2))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 2
        + (n.choose 3 : ℤ) * (b ^ (n * (n - 3)) + a ^ (n * (n - 3)) + h ^ (n - 3))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 3
        [ZMOD (n : ℤ) ^ (4 * s + 1)] := by
  obtain ⟨Ta, hTa, hA⟩ :=
    M1F3_expand_trunc hn (by omega) hs (r := 3) (by omega) (a ^ n) (a * b * c * k)
  obtain ⟨Tb, hTb, hB⟩ :=
    M1F3_expand_trunc hn (by omega) hs (r := 3) (by omega) (b ^ n) (a * b * c * k)
  obtain ⟨Th, hTh, hH⟩ :=
    M1F3_expand_trunc hn (by omega) hs (r := 3) (by omega) h (-(a * b * c * k))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    Nat.sub_zero, pow_zero, pow_one, mul_one, zero_add] at hA hB hH
  have hsign : h - (n : ℤ) ^ s * (a * b * c * k)
      = h + (n : ℤ) ^ s * (-(a * b * c * k)) := by ring
  rw [hsign] at hsol
  have hpa : (a ^ n) ^ n = a ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hpb : (b ^ n) ^ n = b ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hpa1 : (a ^ n) ^ (n - 1) = a ^ (n * (n - 1)) := by rw [← pow_mul]
  have hpb1 : (b ^ n) ^ (n - 1) = b ^ (n * (n - 1)) := by rw [← pow_mul]
  have hpa2 : (a ^ n) ^ (n - 2) = a ^ (n * (n - 2)) := by rw [← pow_mul]
  have hpb2 : (b ^ n) ^ (n - 2) = b ^ (n * (n - 2)) := by rw [← pow_mul]
  have hpa3 : (a ^ n) ^ (n - 3) = a ^ (n * (n - 3)) := by rw [← pow_mul]
  have hpb3 : (b ^ n) ^ (n - 3) = b ^ (n * (n - 3)) := by rw [← pow_mul]
  rw [hpa, hpa1, hpa2, hpa3] at hA
  rw [hpb, hpb1, hpb2, hpb3] at hB
  have hkey : h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
      = (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
            * ((n : ℤ) ^ s * (a * b * c * k))
        + (n.choose 2 : ℤ) * (b ^ (n * (n - 2)) + a ^ (n * (n - 2)) - h ^ (n - 2))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 2
        + (n.choose 3 : ℤ) * (b ^ (n * (n - 3)) + a ^ (n * (n - 3)) + h ^ (n - 3))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 3
        + (Ta + Tb - Th) := by
    linarith [hA, hB, hH, hsol]
  have hdiv : (n : ℤ) ^ (4 * s + 1) ∣ Ta + Tb - Th :=
    dvd_add (dvd_add hTa hTb) (dvd_neg.mpr hTh)
  have hfin : (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
            * ((n : ℤ) ^ s * (a * b * c * k))
        + (n.choose 2 : ℤ) * (b ^ (n * (n - 2)) + a ^ (n * (n - 2)) - h ^ (n - 2))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 2
        + (n.choose 3 : ℤ) * (b ^ (n * (n - 3)) + a ^ (n * (n - 3)) + h ^ (n - 3))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 3
        - (h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2))
      = -(Ta + Tb - Th) := by
    linarith [hkey]
  rw [Int.modEq_iff_dvd, hfin]
  exact dvd_neg.mpr hdiv

/-- **S2** — the printed (10) (author p. 6, region `P006-R2`): the same identity
at `r = 4`, with the `X`-linear term moved to the **left-hand side** as printed,
and modulus `n^{5s+1}`.

"`h^n - a^{n^2} - b^{n^2} - n[a^{n(n-1)} + b^{n(n-1)} + h^{n-1}] n^s abck
≡ (n(n-1)/2)[...](n^s abck)^2 + (n(n-1)(n-2)/6)[...](n^s abck)^3
+ (n(n-1)(n-2)(n-3)/24)[...](n^s abck)^4 (mod n^{5s+1})`" -/
theorem M1F3_step_S2_ten {n s : ℕ} {a b c k h : ℤ}
    (hn : Nat.Prime n) (hn11 : 11 < n) (hs : 1 ≤ s)
    (hsol : (a ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
        + (b ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
      = (h - (n : ℤ) ^ s * (a * b * c * k)) ^ n) :
    h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
        - (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
            * ((n : ℤ) ^ s * (a * b * c * k))
      ≡ (n.choose 2 : ℤ) * (b ^ (n * (n - 2)) + a ^ (n * (n - 2)) - h ^ (n - 2))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 2
        + (n.choose 3 : ℤ) * (b ^ (n * (n - 3)) + a ^ (n * (n - 3)) + h ^ (n - 3))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 3
        + (n.choose 4 : ℤ) * (b ^ (n * (n - 4)) + a ^ (n * (n - 4)) - h ^ (n - 4))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 4
        [ZMOD (n : ℤ) ^ (5 * s + 1)] := by
  obtain ⟨Ta, hTa, hA⟩ :=
    M1F3_expand_trunc hn (by omega) hs (r := 4) (by omega) (a ^ n) (a * b * c * k)
  obtain ⟨Tb, hTb, hB⟩ :=
    M1F3_expand_trunc hn (by omega) hs (r := 4) (by omega) (b ^ n) (a * b * c * k)
  obtain ⟨Th, hTh, hH⟩ :=
    M1F3_expand_trunc hn (by omega) hs (r := 4) (by omega) h (-(a * b * c * k))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    Nat.sub_zero, pow_zero, pow_one, mul_one, zero_add] at hA hB hH
  have hsign : h - (n : ℤ) ^ s * (a * b * c * k)
      = h + (n : ℤ) ^ s * (-(a * b * c * k)) := by ring
  rw [hsign] at hsol
  have hpa : (a ^ n) ^ n = a ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hpb : (b ^ n) ^ n = b ^ (n ^ 2) := by rw [← pow_mul, pow_two]
  have hpa1 : (a ^ n) ^ (n - 1) = a ^ (n * (n - 1)) := by rw [← pow_mul]
  have hpb1 : (b ^ n) ^ (n - 1) = b ^ (n * (n - 1)) := by rw [← pow_mul]
  have hpa2 : (a ^ n) ^ (n - 2) = a ^ (n * (n - 2)) := by rw [← pow_mul]
  have hpb2 : (b ^ n) ^ (n - 2) = b ^ (n * (n - 2)) := by rw [← pow_mul]
  have hpa3 : (a ^ n) ^ (n - 3) = a ^ (n * (n - 3)) := by rw [← pow_mul]
  have hpb3 : (b ^ n) ^ (n - 3) = b ^ (n * (n - 3)) := by rw [← pow_mul]
  have hpa4 : (a ^ n) ^ (n - 4) = a ^ (n * (n - 4)) := by rw [← pow_mul]
  have hpb4 : (b ^ n) ^ (n - 4) = b ^ (n * (n - 4)) := by rw [← pow_mul]
  rw [hpa, hpa1, hpa2, hpa3, hpa4] at hA
  rw [hpb, hpb1, hpb2, hpb3, hpb4] at hB
  have hkey : h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
      = (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
            * ((n : ℤ) ^ s * (a * b * c * k))
        + (n.choose 2 : ℤ) * (b ^ (n * (n - 2)) + a ^ (n * (n - 2)) - h ^ (n - 2))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 2
        + (n.choose 3 : ℤ) * (b ^ (n * (n - 3)) + a ^ (n * (n - 3)) + h ^ (n - 3))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 3
        + (n.choose 4 : ℤ) * (b ^ (n * (n - 4)) + a ^ (n * (n - 4)) - h ^ (n - 4))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 4
        + (Ta + Tb - Th) := by
    linarith [hA, hB, hH, hsol]
  have hdiv : (n : ℤ) ^ (5 * s + 1) ∣ Ta + Tb - Th :=
    dvd_add (dvd_add hTa hTb) (dvd_neg.mpr hTh)
  have hfin :
      ((n.choose 2 : ℤ) * (b ^ (n * (n - 2)) + a ^ (n * (n - 2)) - h ^ (n - 2))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 2
        + (n.choose 3 : ℤ) * (b ^ (n * (n - 3)) + a ^ (n * (n - 3)) + h ^ (n - 3))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 3
        + (n.choose 4 : ℤ) * (b ^ (n * (n - 4)) + a ^ (n * (n - 4)) - h ^ (n - 4))
            * ((n : ℤ) ^ s * (a * b * c * k)) ^ 4)
        - (h ^ n - a ^ (n ^ 2) - b ^ (n ^ 2)
            - (n : ℤ) * (a ^ (n * (n - 1)) + b ^ (n * (n - 1)) + h ^ (n - 1))
                * ((n : ℤ) ^ s * (a * b * c * k)))
      = -(Ta + Tb - Th) := by
    linarith [hkey]
  rw [Int.modEq_iff_dvd, hfin]
  exact dvd_neg.mpr hdiv

end M1F3

-- DONE-flip evidence: permitted axioms only, and no `sorryAx`.
#print axioms M1F3.M1F3_step_S0_eight
#print axioms M1F3.M1F3_step_S1_nine
#print axioms M1F3.M1F3_step_S2_ten
