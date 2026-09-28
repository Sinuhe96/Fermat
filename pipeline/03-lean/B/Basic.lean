/-
Chunk `B-01` — section B, `P002-R1` (p. 2): the two sum-transformation rules the
main proof cites as "áp dụng mục B.1/B.2, trang 2" (pp. 9, 10, 11, 13, 14).

The Vietnamese source text lives in `pipeline/02-chunks/chunks/B-01.yml` (byte
copy of the signed region record), never retyped here.

  B.1  Σ_{i=k}^{n} a_i = Σ_{i=m}^{n+m-k} a_{i-m+k},  k, m ∈ ℕ
  B.2  Σ_{i=k}^{m-1} i(i-1)...(i-k+1) h^{m-1-i} x^{i-k}
         = Σ_{i=0}^{m-1-k} (m-1-i)(m-2-i)...(m-k-i) h^i x^{m-1-k-i}
         = f^{(k)}(x),   k ∈ ℕ*, m ≥ 2,
       with f(x) = x^{m-1} + h x^{m-2} + ... + h^{m-1} = (x^m - h^m)/(x - h).

Encoding notes (paper convention made explicit; F2/F3 per AGENTS.md):

* **B.1 is stated in the range form both sides share.** The printed display is
  the index shift `i ↦ i - m + k` between `[k, n]` and `[m, n+m-k]`; the two
  ranges have the same cardinality `n+1-k`, so the rule is equivalently "the
  same list, shifted by `k-m`", which is what the main proof applies (it uses
  B.1 to re-index `Σ_{i=…}` in pp. 12–14). `Finset.range` is the form the rest
  of this repo's sums are built on, so the range form is the one stated: with
  `N := n + 1 - k` both sides are sums over `Finset.range N`. The literal
  `Icc`-form was written first and abandoned for a measured reason: its range
  equality `(n + 1) - k = (n + m - k + 1) - m` is true in ℕ but `omega` reports a
  spurious counterexample for it (truncated subtraction is not linear), so it
  would have needed a hand-rolled case split whose only content is ℕ bookkeeping,
  not the author's rule.
* the printed `Σ_{i=k}^{m-1}` in B.2 is exactly `Finset.Ico k m`;
* the falling factorial `i(i-1)...(i-k+1)` is `Nat.descFactorial i k`;
* B.2's printed right range `Σ_{i=0}^{m-1-k}` is non-empty only when `k ≤ m-1`,
  which the paper leaves implicit. `B_step_S1_reindex` takes `k ≤ m-1`
  explicitly: without it the printed equality is *false* in ℕ, since `m-1-k`
  truncates to `0` while the left range is empty.
-/
import Mathlib

-- name pin for B.1 / B.2 (all eight confirmed by the round that ran this block;
-- `Finset.sum_Icc_eq_sum_range` does NOT exist at this pin — checked against the
-- pinned Mathlib source before writing, which cost 1 s instead of a round)
#check @Finset.sum_Ico_eq_sum_range
#check @Finset.sum_range_reflect
#check @Finset.sum_congr
#check @Finset.mem_Ico
#check @Finset.mem_range
#check @Nat.descFactorial
#check @Nat.descFactorial_succ
#check @Polynomial.derivative

namespace B

/-- **B.1** (author p. 2, `P002-R1`, rule 1).

"Σ_{i=k}^{n} a_i = Σ_{i=m}^{n+m-k} a_{i-m+k}, k, m ∈ ℕ" — the index shift, in
the range form both sides share (see the header). The map `i ↦ i + (m - k)` is
a bijection from `[k, n]` onto `[m, n+m-k]`, and no side condition is needed:
both sums are empty when `k > n`, and `(m + i) - m = i` with the shift applied
is what makes the two summands the same. -/
theorem B_step_S0_index_shift (a : ℕ → ℤ) (k m N : ℕ) :
    (∑ i ∈ Finset.range N, a (k + i))
      = ∑ i ∈ Finset.range N, a (m + i - m + k) := by
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  omega

/-- **B.2**, first equality (author p. 2, `P002-R1`, rule 2).

The falling-factorial sum read backwards: `i ↦ m-1-i` maps the printed left
range `[k, m-1]` onto the printed right range `[0, m-1-k]` and takes
`h^{m-1-i} x^{i-k}` to `h^i x^{m-1-k-i}`; the falling factorial matches because
the same substituted index `m-1-i` appears in it. `(i)_k` is
`Nat.descFactorial i k`, which is `0` for `i < k` — so the printed left range
starting at `i = k` loses nothing.

`1 ≤ k` is the print's `k ∈ ℕ*`; `k ≤ m-1` is the implicit condition discussed in
the header. -/
theorem B_step_S1_reindex (m k : ℕ) (hk : 1 ≤ k) (_hkm : k ≤ m - 1) (x h : ℤ) :
    (∑ i ∈ Finset.Ico k m,
        ((i.descFactorial k : ℕ) : ℤ) * h ^ (m - 1 - i) * x ^ (i - k))
      = ∑ i ∈ Finset.range (m - k),
          (((m - 1 - i).descFactorial k : ℕ) : ℤ) * h ^ i * x ^ (m - 1 - k - i) := by
  rw [Finset.sum_Ico_eq_sum_range]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.mem_range] at hi
  have e1 : k + (m - k - 1 - i) = m - 1 - i := by omega
  have e2 : m - 1 - (m - 1 - i) = i := by omega
  have e3 : m - 1 - i - k = m - 1 - k - i := by omega
  rw [e1, e2, e3]

/-- The paper's `f` (author p. 2, `P002-R1`, rule 2):
`f(x) = x^{m-1} + h x^{m-2} + ... + h^{m-1}`, encoded as the sum whose
`X^{m-1-t}` coefficient is `h^t` — the paper's ordering, read off the printed
expansion. -/
noncomputable def Bf (m : ℕ) (h : ℤ) : Polynomial ℤ :=
  ∑ t ∈ Finset.range m, Polynomial.C (h ^ t) * Polynomial.X ^ (m - 1 - t)

/-- **B.2**, second equality (author p. 2, `P002-R1`, rule 2):
`Σ_{i=0}^{m-1-k} (m-1-i)(m-2-i)...(m-k-i) h^i x^{m-1-k-i} = f^{(k)}(x)`.

Two elementary facts, in the author's order: differentiating `X^{m-1-t}`
`k` times gives `(m-1-t)(m-2-t)...(m-k-t) X^{m-1-t-k}`
(`Polynomial.iterate_derivative_X_pow_eq_smul`, with the falling factorial
`Nat.descFactorial`), and the printed upper limit `m-1-k` is exactly where the
falling factorial dies — `(m-1-i)_k = 0` for `i ≥ m-k`
(`Nat.descFactorial_eq_zero_iff_lt`) — so the sum over `range m` drops precisely
those terms. No new mathematics: (a) evaluation of one monomial derivative,
(b) a vanishing tail. `1 ≤ k` is the print's `k ∈ ℕ*`. -/
theorem B_step_S2_deriv (m k : ℕ) (_hk : 1 ≤ k) (hkm : k ≤ m - 1) (x h : ℤ) :
    (∑ i ∈ Finset.range (m - k),
        (((m - 1 - i).descFactorial k : ℕ) : ℤ) * h ^ i * x ^ (m - 1 - k - i))
      = (Polynomial.derivative^[k] (Bf m h)).eval x := by
  -- (a) the k-th derivative of each monomial, evaluated
  have hterm : ∀ t ∈ Finset.range m,
      (Polynomial.derivative^[k] (Polynomial.C (h ^ t) * Polynomial.X ^ (m - 1 - t))).eval x
        = h ^ t * (((m - 1 - t).descFactorial k : ℕ) : ℤ) * x ^ (m - 1 - t - k) := by
    intro t _
    simp only [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_smul,
      Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    ring
  -- (b) the tail beyond `m - k` vanishes, which is the printed upper limit
  have htail : (∑ t ∈ Finset.range m,
        h ^ t * (((m - 1 - t).descFactorial k : ℕ) : ℤ) * x ^ (m - 1 - t - k))
      = ∑ t ∈ Finset.range (m - k),
          h ^ t * (((m - 1 - t).descFactorial k : ℕ) : ℤ) * x ^ (m - 1 - t - k) := by
    -- `sum_subset` concludes `∑ over the SMALLER set = ∑ over the larger`
    -- (measured: `s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑_{s₁} = ∑_{s₂}`),
    -- so the `.symm` is what puts the `range m` sum on the left.
    refine (Finset.sum_subset ?_ ?_).symm
    · intro y hy
      simp only [Finset.mem_range] at hy ⊢
      omega
    · intro y hy hynot
      simp only [Finset.mem_range] at hy hynot
      -- `omega` cannot relate `m - 1 - y` to `y ≥ m - k` (truncated-subtraction
      -- monotonicity; the same weakness that forced B.1's range form), so the
      -- comparison is built from core lemmas: pass to `m - (y + 1) < k`,
      -- convert with `tsub_lt_iff_right`, and leave `omega` only the linear part.
      have hyge : m - k ≤ y := Nat.le_of_not_lt hynot
      have hk_le : k ≤ m := Nat.le_trans hkm (Nat.sub_le m 1)
      have hyk : m ≤ y + k := by
        calc m = m - k + k := (tsub_add_cancel_of_le hk_le).symm
          _ ≤ y + k := Nat.add_le_add_right hyge k
      have hy1 : y + 1 ≤ m := Nat.succ_le_iff.mpr hy
      have hlt : m - 1 - y < k := by
        rw [Nat.sub_sub, Nat.add_comm 1 y, tsub_lt_iff_right hy1]
        omega
      rw [Nat.descFactorial_of_lt hlt]
      simp
  unfold Bf
  rw [Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum]
  rw [Finset.sum_congr rfl hterm, htail]
  refine Finset.sum_congr rfl ?_
  intro i _
  have e : m - 1 - k - i = m - 1 - i - k := by omega
  rw [e]
  ring

end B

-- DONE evidence for `B-01`: the three declarations must rest on the permitted
-- axioms only (propext, Classical.choice, Quot.sound).  Printed in the same
-- round as the proofs so the log is the certificate (M1_LANE.md §1).
#print axioms B.B_step_S0_index_shift
#print axioms B.B_step_S1_reindex
#print axioms B.B_step_S2_deriv
