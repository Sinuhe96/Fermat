import Mathlib

/-!
# Lemma 2 (bo de 2) - the author's proof: S0 + S1 + S2, then the assembly

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 1 ("Bo de 2: ..." - full literal transcription in
    `pipeline/02-chunks/chunks/L2-01.yml`, verified against the 300 dpi
    renders `page-001-300dpi-full.png` / `page-002-300dpi-full.png`
    (two reads: render + pypdf text layer));
  * proof section 2 "Chung minh bo de 2": p. 2.

Statement (normalised reading, exact Vietnamese in the chunk YAML):

  If n : nat with n >= 3, and the equation x^n + y^n = z^n has no
  nonzero integer solution, then for every k >= 1 the equation
  x^{n*k} + y^{n*k} = z^{n*k} also has no nonzero integer solution.

Ordered step map (one named declaration per author step, S0-S3):

  S0  Assume there is a positive integer k0 such that
      x^{n*k0} + y^{n*k0} = z^{n*k0} has the nonzero integer solution
      (u, v, t).                                           -> hypothesis of L2_step_S1
  S1  Then u^{n*k0} + v^{n*k0} = t^{n*k0} iff
      (u^k0)^n + (v^k0)^n = (t^k0)^n.                      -> L2_step_S1
  S2  Hence x^n + y^n = z^n has the nonzero integer solution
      (u^k0, v^k0, t^k0).                                  -> conclusion of L2_step_S1
  S3  This contradicts the hypothesis.                      -> L2_bo_de_2 (assembly)

The display line S1 is written by the author with an equivalence arrow;
the deduction actually used is, coordinate by coordinate, the identity
`(u^k)^n = u^(k*n)` (pin `pow_mul`: `a ^ (m * n) = (a ^ m) ^ n`,
rewrite applied directly — the paper's `nk` matches `k * n`). The step
theorem below formalises exactly that.

Nothing here is our own mathematics: the content is the author's chain.
The only formal additions are the implicit side conditions the paper
leaves to convention (the nonzero coordinates stay nonzero after
exponentiation - the author's k0 is positive, so `k != 0` is carried in
the statement; no zero exponent issue arises because `(u^k)^n = u^(k*n)`
holds for every k, n : nat).
-/

namespace L2

/-- **S1** (author p. 2, section 2, display line).

From a nonzero integer solution `(u,v,t)` of
`x^(k*n) + y^(k*n) = z^(k*n)` the author produces the nonzero integer
solution `(u^k, v^k, t^k)` of `x^n + y^n = z^n`:

  u^{n*k0} + v^{n*k0} = t^{n*k0}  <=>  (u^k0)^n + (v^k0)^n = (t^k0)^n

The displayed equivalence is the identity `(u^k)^n = u^(k*n)` applied
coordinate-wise; the nonzero claims are the author's "nonzero integer
solution" requirement preserved under exponentiation. -/
theorem L2_step_S1 {n k : ℕ} {u v t : ℤ}
    (hu : u ≠ 0) (hv : v ≠ 0) (ht : t ≠ 0)
    (hsol : u ^ (k * n) + v ^ (k * n) = t ^ (k * n)) :
    u ^ k ≠ 0 ∧ v ^ k ≠ 0 ∧ t ^ k ≠ 0 ∧
      (u ^ k) ^ n + (v ^ k) ^ n = (t ^ k) ^ n := by
  refine ⟨pow_ne_zero k hu, pow_ne_zero k hv, pow_ne_zero k ht, ?_⟩
  rw [pow_mul, pow_mul, pow_mul] at hsol
  exact hsol

/-- **Bo de 2** - the author's statement (p. 1), proved by the p. 2 chain
S0-S3.

The author argues by contrapositive: a nonzero solution of the `k*n`
equation (S0) gives, by `L2_step_S1`, a nonzero solution of the `n`
equation (S1+S2), contradicting the hypothesis (S3). -/
theorem L2_bo_de_2 {n k : ℕ} (_hn : 3 ≤ n) (_hk : k ≠ 0)
    (hno : ¬ ∃ u v t : ℤ, u ≠ 0 ∧ v ≠ 0 ∧ t ≠ 0 ∧ u ^ n + v ^ n = t ^ n) :
    ¬ ∃ u v t : ℤ,
      u ≠ 0 ∧ v ≠ 0 ∧ t ≠ 0 ∧ u ^ (k * n) + v ^ (k * n) = t ^ (k * n) := by
  intro h
  obtain ⟨u, v, t, hu, hv, ht, hsol⟩ := h
  obtain ⟨hu', hv', ht', hsol'⟩ := L2_step_S1 hu hv ht hsol
  exact hno ⟨u ^ k, v ^ k, t ^ k, hu', hv', ht', hsol'⟩

#print axioms L2.L2_step_S1
#print axioms L2.L2_bo_de_2

end L2