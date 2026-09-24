import Mathlib

/-!
# Lemma 1 (bổ đề 1) — the author's proof, step S0+S1

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 1 ("Bổ đề 1: ... (u, v) = (u, t) = (v, t) = 1");
  * proof §1 "Chứng minh bổ đề 1": p. 2.

Transcription + ordered step map: `pipeline/02-chunks/chunks/L1-01.yml`
(S0–S6). One named declaration per author step, all classified S1:

  S0+S1  "Giả sử tồn tại số nguyên n lớn hơn 2, sao cho PT(1) có
          x = u₀, y = v₀, z = t₀ là một nghiệm nguyên khác không và
          (u₀, v₀, t₀) = d. Khi đó tồn tại ba số u, v, t ∈ ℤ* sao cho
          (u, v, t) = 1, u₀ = ud, v₀ = vd, t₀ = td và u₀ⁿ + v₀ⁿ = t₀ⁿ,
          suy ra uⁿ + vⁿ = tⁿ (1''), suy ra x = u, y = v, z = t là một
          nghiệm nguyên khác không của PT(1)."
                                             -> L1_reduce_coprime
  S2+S3  "Giả sử (u, v) = d', từ (1'') suy ra tⁿ ⋮ d'ⁿ"  -> L1_step_S2_S3
  S4     "suy ra t ⋮ d'"                                 -> L1_step_S4
  S5     "mà (u, v, t) = 1 nên d′ = 1. Vậy (u, v) = 1."  -> L1_step_S5
  S6     "Chứng minh tương tự ta cũng có (u, t) = (t, v) = 1."
                                                         -> L1_step_S6
  assembly of all of the above           -> L1_bo_de_1 (author's order)

Term mapping and the reusable proof patterns for the next chunks:
`pipeline/03-lean/ENCODING_MAP.md` §B.

Nothing here is our own mathematics: the content is the author's chain.
The only formal additions are the implicit side conditions the paper
leaves to convention (d ≠ 0, the maximality of `Int.gcd`, cancellation by
dⁿ ≠ 0, and `n ≠ 0` at S4, which the author's `n ≥ 3` supplies).

Triple gcd notation: the author's `(u₀, v₀, t₀) = d` is encoded as
`Int.gcd u₀ (Int.gcd v₀ t₀)` (nested binary gcd; `Int.gcd` is ℕ-valued),
and the author's conclusion `(u, v, t) = 1` likewise. `(x, y, z) = 1`
means "no common divisor", i.e. `Int.gcd x (Int.gcd y z) = 1`.
-/

namespace L1

/-- **S0 + S1** (author p. 2, first paragraph).

A nonzero integer solution `(u₀,v₀,t₀)` of `xⁿ + yⁿ = zⁿ` divided by its
common gcd `d := (u₀,v₀,t₀)` yields a nonzero integer solution `(u,v,t)`
of the same equation with `(u,v,t) = 1`.

The author's hypothesis `n > 2` (statement: `n ≥ 3`) is carried as `_hn`:
this reduction step does not use it, but the author states it here, so it
stays in the claim. -/
theorem L1_reduce_coprime
    {n : ℕ} (_hn : 3 ≤ n) {u₀ v₀ t₀ : ℤ}
    (hu₀ : u₀ ≠ 0) (hv₀ : v₀ ≠ 0) (ht₀ : t₀ ≠ 0)
    (hsol : u₀ ^ n + v₀ ^ n = t₀ ^ n) :
    ∃ u v t : ℤ,
      u ≠ 0 ∧ v ≠ 0 ∧ t ≠ 0 ∧
      Int.gcd u ((Int.gcd v t : ℕ) : ℤ) = 1 ∧
      u₀ = u * ↑(Int.gcd u₀ ((Int.gcd v₀ t₀ : ℕ) : ℤ)) ∧
      v₀ = v * ↑(Int.gcd u₀ ((Int.gcd v₀ t₀ : ℕ) : ℤ)) ∧
      t₀ = t * ↑(Int.gcd u₀ ((Int.gcd v₀ t₀ : ℕ) : ℤ)) ∧
      u ^ n + v ^ n = t ^ n := by
  -- "và (u₀, v₀, t₀) = d": the author's triple gcd.
  set D : ℕ := Int.gcd u₀ ((Int.gcd v₀ t₀ : ℕ) : ℤ) with hD
  set G : ℕ := Int.gcd v₀ t₀ with hG

  -- d divides each coordinate: gcd_dvd_left/right composed through the nesting.
  have hDdvd₀ : (D : ℤ) ∣ u₀ := by
    rw [hD]; exact Int.gcd_dvd_left u₀ ((G : ℕ) : ℤ)
  have hDdvdG : (D : ℤ) ∣ (G : ℤ) := by
    rw [hD]; exact Int.gcd_dvd_right u₀ ((G : ℕ) : ℤ)
  have hGdvdv : (G : ℤ) ∣ v₀ := by
    rw [hG]; exact Int.gcd_dvd_left v₀ t₀
  have hGdvdt : (G : ℤ) ∣ t₀ := by
    rw [hG]; exact Int.gcd_dvd_right v₀ t₀
  have hDdvdv : (D : ℤ) ∣ v₀ := dvd_trans hDdvdG hGdvdv
  have hDdvdt : (D : ℤ) ∣ t₀ := dvd_trans hDdvdG hGdvdt

  -- [implicit side condition] d ≠ 0: it divides the nonzero u₀.
  have hDne : D ≠ 0 := by
    intro h0
    have hz : (0 : ℤ) ∣ u₀ := by
      have := hDdvd₀
      rw [h0] at this
      simpa using this
    exact hu₀ (zero_dvd_iff.mp hz)

  -- "Khi đó tồn tại ba số u, v, t ∈ ℤ* ... u₀ = ud, v₀ = vd, t₀ = td"
  obtain ⟨u, hu⟩ := hDdvd₀
  obtain ⟨v, hv⟩ := hDdvdv
  obtain ⟨t, ht⟩ := hDdvdt
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact hu₀ hu
  have hv_ne : v ≠ 0 := by
    intro h
    rw [h, mul_zero] at hv
    exact hv₀ hv
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h, mul_zero] at ht
    exact ht₀ ht

  -- "suy ra uⁿ + vⁿ = tⁿ (1'')": divide u₀ⁿ + v₀ⁿ = t₀ⁿ by dⁿ.
  have hsol' : u ^ n + v ^ n = t ^ n := by
    have key : ((D : ℤ) ^ n) * (u ^ n + v ^ n) = ((D : ℤ) ^ n) * t ^ n := by
      rw [mul_add, ← mul_pow, ← mul_pow, ← mul_pow]
      rw [← hu, ← hv, ← ht]
      exact hsol
    have hDnne : (D : ℤ) ^ n ≠ 0 := pow_ne_zero n (by exact_mod_cast hDne)
    exact mul_left_cancel₀ hDnne key

  -- "sao cho (u, v, t) = 1": gcd maximality — the only real content of S1.
  have hnew : Int.gcd u ((Int.gcd v t : ℕ) : ℤ) = 1 := by
    set H : ℕ := Int.gcd v t with hH
    set e : ℕ := Int.gcd u ((H : ℕ) : ℤ) with he
    -- e divides u, v, t
    have hedvdu : (e : ℤ) ∣ u := by
      rw [he]; exact Int.gcd_dvd_left u ((H : ℕ) : ℤ)
    have hedvdH : (e : ℤ) ∣ (H : ℤ) := by
      rw [he]; exact Int.gcd_dvd_right u ((H : ℕ) : ℤ)
    have hHdvdv : (H : ℤ) ∣ v := by
      rw [hH]; exact Int.gcd_dvd_left v t
    have hHdvdt : (H : ℤ) ∣ t := by
      rw [hH]; exact Int.gcd_dvd_right v t
    have hedvdv : (e : ℤ) ∣ v := dvd_trans hedvdH hHdvdv
    have hedvdt : (e : ℤ) ∣ t := dvd_trans hedvdH hHdvdt
    -- D is the GREATEST common divisor of u₀, v₀, t₀ (the author's "d").
    have hmax : ∀ m : ℕ, (m : ℤ) ∣ u₀ → (m : ℤ) ∣ v₀ → (m : ℤ) ∣ t₀ → m ∣ D := by
      intro m h1 h2 h3
      have h4 : m ∣ Int.gcd v₀ t₀ := Int.dvd_gcd h2 h3
      have h5 : m ∣ Int.gcd u₀ ((Int.gcd v₀ t₀ : ℕ) : ℤ) :=
        Int.dvd_gcd h1 (by exact_mod_cast h4)
      simpa only [hD] using h5
    -- e·d is again a common divisor of u₀, v₀, t₀ (since u₀ = d·u, e ∣ u).
    have heDvd₀ : ((e * D : ℕ) : ℤ) ∣ u₀ := by
      obtain ⟨s, hs⟩ := hedvdu
      refine ⟨s, ?_⟩
      rw [hu, hs]; push_cast; ring
    have heDvdv₀ : ((e * D : ℕ) : ℤ) ∣ v₀ := by
      obtain ⟨s, hs⟩ := hedvdv
      refine ⟨s, ?_⟩
      rw [hv, hs]; push_cast; ring
    have heDvdt₀ : ((e * D : ℕ) : ℤ) ∣ t₀ := by
      obtain ⟨s, hs⟩ := hedvdt
      refine ⟨s, ?_⟩
      rw [ht, hs]; push_cast; ring
    -- maximality forces e·d ∣ d, hence e ∣ 1, hence e = 1.
    have hEmul : (e * D) ∣ D := hmax (e * D) heDvd₀ heDvdv₀ heDvdt₀
    obtain ⟨k, hk⟩ := hEmul
    have hk' : (e * k) * D = 1 * D := by
      rw [one_mul]
      calc (e * k) * D = e * D * k := by ring
        _ = D := hk.symm
    have hek : e * k = 1 := mul_right_cancel₀ hDne hk'
    exact Nat.dvd_one.mp ⟨k, hek.symm⟩

  exact ⟨u, v, t, hu_ne, hv_ne, ht_ne, hnew,
    by rw [hu, mul_comm], by rw [hv, mul_comm], by rw [ht, mul_comm], hsol'⟩

/-- **S2 + S3** (author p. 2, second paragraph).

"Giả sử (u, v) = d', từ (1'') suy ra tⁿ ⋮ d'ⁿ" — from `uⁿ + vⁿ = tⁿ` and
`d' = (u,v)` (so `d' ∣ u` and `d' ∣ v`) we get `d'ⁿ ∣ tⁿ`.

S2 is only the naming of `d' := (u,v)`; all content is S3. -/
theorem L1_step_S2_S3 {n : ℕ} {u v t : ℤ}
    (hsol : u ^ n + v ^ n = t ^ n) :
    ((Int.gcd u v : ℕ) : ℤ) ^ n ∣ t ^ n := by
  set dd : ℕ := Int.gcd u v with hd
  have hdvdv : (dd : ℤ) ∣ u := by
    rw [hd]; exact Int.gcd_dvd_left u v
  have hdvdt : (dd : ℤ) ∣ v := by
    rw [hd]; exact Int.gcd_dvd_right u v
  -- d'ⁿ ∣ uⁿ and d'ⁿ ∣ vⁿ
  have h1 : (dd : ℤ) ^ n ∣ u ^ n := pow_dvd_pow_of_dvd hdvdv n
  have h2 : (dd : ℤ) ^ n ∣ v ^ n := pow_dvd_pow_of_dvd hdvdt n
  -- hence d'ⁿ ∣ uⁿ + vⁿ = tⁿ
  have h3 : (dd : ℤ) ^ n ∣ t ^ n := by
    rw [← hsol]
    exact dvd_add h1 h2
  simpa only [hd] using h3

/-- **S4** (author p. 2, second paragraph).

"suy ra tⁿ ⋮ d'ⁿ, suy ra t ⋮ d'" — from `d'ⁿ ∣ tⁿ` conclude `d' ∣ t`.
Stated for `n ≠ 0`, which the author has (`n ≥ 3`): the implication is
FALSE for `n = 0` (`a⁰ = 1 ∣ b⁰ = 1` while `a ∤ b`). Per AGENTS.md this is
an F3 side condition traced to the author's own hypothesis, not an added
assumption. -/
theorem L1_step_S4 {n : ℕ} (hn : n ≠ 0) {d : ℕ} {t : ℤ}
    (h : (d : ℤ) ^ n ∣ t ^ n) : (d : ℤ) ∣ t := by
  -- move to ℕ through natAbs: |dⁿ| ∣ |tⁿ| ⟺ dⁿ ∣ |t|ⁿ
  have hN : d ^ n ∣ t.natAbs ^ n := by
    have h' := (Int.natAbs_dvd_natAbs).mpr h
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using h'
  have hdvd : d ∣ t.natAbs := by
    by_cases hB : t.natAbs = 0
    · rw [hB]; exact dvd_zero d
    by_cases hd : d = 0
    · -- d = 0 with n ≠ 0 forces t = 0, contradicting t.natAbs ≠ 0
      exfalso
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [hd, pow_succ, mul_zero, zero_dvd_iff] at hN
      exact (pow_ne_zero (m + 1) hB) hN
    · -- exponent vectors: d.factorization ≤ t.natAbs.factorization pointwise
      refine (Nat.factorization_le_iff_dvd hd hB).mp ?_
      have h1 : (d ^ n).factorization ≤ (t.natAbs ^ n).factorization :=
        (Nat.factorization_le_iff_dvd (pow_ne_zero n hd) (pow_ne_zero n hB)).mpr hN
      simp only [Nat.factorization_pow] at h1
      simp only [Finsupp.le_def] at h1 ⊢
      intro p
      have hp := h1 p
      simp only [Finsupp.smul_apply, nsmul_eq_mul] at hp
      exact Nat.le_of_mul_le_mul_left hp (Nat.pos_iff_ne_zero.mpr hn)
  exact (Int.natAbs_dvd_natAbs).mp (by simpa only [Int.natAbs_natCast] using hdvd)

/-- **S5** (author p. 2, second paragraph).

"mà (u, v, t) = 1 nên d′ = 1. Vậy (u, v) = 1."

The author applies this at `d′ = (u,v)`: `d′ ∣ u` and `d′ ∣ v` hold by
definition of the gcd, `d′ ∣ t` is S4's conclusion, and `(u,v,t) = 1` kills
`d′`. Stated once for an arbitrary `d` dividing all three coordinates,
because S6 ("chứng minh tương tự") needs the same inference for the pairs
`(u,t)` and `(v,t)`. -/
theorem L1_step_S5 {u v t : ℤ} {d : ℕ}
    (hu : (d : ℤ) ∣ u) (hv : (d : ℤ) ∣ v) (ht : (d : ℤ) ∣ t)
    (hcop : Int.gcd u ((Int.gcd v t : ℕ) : ℤ) = 1) : d = 1 := by
  -- d ∣ (v,t) then d ∣ (u,(v,t)) = 1  (ℤ-level: Int.dvd_coe_gcd)
  have h1 : (d : ℤ) ∣ ((Int.gcd v t : ℕ) : ℤ) := Int.dvd_coe_gcd hv ht
  have h2 : (d : ℤ) ∣ ((Int.gcd u ((Int.gcd v t : ℕ) : ℤ) : ℕ) : ℤ) :=
    Int.dvd_coe_gcd hu h1
  have h3 : (d : ℤ) ∣ (1 : ℤ) := by simpa [hcop] using h2
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp h3)

/-- **S6** (author p. 2, third line): "Chứng minh tương tự ta cũng có
(u, t) = (t, v) = 1."

Same template as S2–S5 with the roles permuted. The paper leaves the
permutation implicit; spelling it out, the third coordinate is reached by
*subtracting* instead of adding:

*  `d″ = (u,t)` divides `u` and `t`, so `d″ⁿ ∣ uⁿ` and `d″ⁿ ∣ tⁿ`;
*  hence `d″ⁿ ∣ tⁿ − uⁿ = vⁿ` (by (1'')), so `d″ ∣ v` (S4);
*  `d″` divides all three while `(u,v,t) = 1`, so `d″ = 1` (S5).
Same for `(v,t)` with `vⁿ − tⁿ = −uⁿ`. -/
theorem L1_step_S6 {n : ℕ} (hn : n ≠ 0) {u v t : ℤ}
    (hsol : u ^ n + v ^ n = t ^ n)
    (hcop : Int.gcd u ((Int.gcd v t : ℕ) : ℤ) = 1) :
    Int.gcd u t = 1 ∧ Int.gcd v t = 1 := by
  -- (u,t): d″ⁿ ∣ tⁿ − uⁿ = vⁿ
  have h_ut_dvd_v : ((Int.gcd u t : ℕ) : ℤ) ∣ v := by
    have h1 : ((Int.gcd u t : ℕ) : ℤ) ^ n ∣ u ^ n :=
      pow_dvd_pow_of_dvd (Int.gcd_dvd_left u t) n
    have h2 : ((Int.gcd u t : ℕ) : ℤ) ^ n ∣ t ^ n :=
      pow_dvd_pow_of_dvd (Int.gcd_dvd_right u t) n
    have h3 : ((Int.gcd u t : ℕ) : ℤ) ^ n ∣ t ^ n - u ^ n := dvd_sub h2 h1
    have h4 : t ^ n - u ^ n = v ^ n := by
      rw [← hsol]; ring
    rw [h4] at h3
    exact L1_step_S4 hn h3
  -- (v,t): d‴ⁿ ∣ vⁿ − tⁿ = −uⁿ
  have h_vt_dvd_u : ((Int.gcd v t : ℕ) : ℤ) ∣ u := by
    have h1 : ((Int.gcd v t : ℕ) : ℤ) ^ n ∣ v ^ n :=
      pow_dvd_pow_of_dvd (Int.gcd_dvd_left v t) n
    have h2 : ((Int.gcd v t : ℕ) : ℤ) ^ n ∣ t ^ n :=
      pow_dvd_pow_of_dvd (Int.gcd_dvd_right v t) n
    have h3 : ((Int.gcd v t : ℕ) : ℤ) ^ n ∣ v ^ n - t ^ n := dvd_sub h1 h2
    have h4 : v ^ n - t ^ n = -(u ^ n) := by
      rw [← hsol]; ring
    rw [h4] at h3
    exact L1_step_S4 hn (dvd_neg.mp h3)
  -- each pair's gcd divides all three coordinates ⇒ equals 1
  exact ⟨L1_step_S5 (d := Int.gcd u t)
          (Int.gcd_dvd_left u t) h_ut_dvd_v (Int.gcd_dvd_right u t) hcop,
        L1_step_S5 (d := Int.gcd v t)
          h_vt_dvd_u (Int.gcd_dvd_left v t) (Int.gcd_dvd_right v t) hcop⟩

/-- **Bổ đề 1** — the author's statement (p. 1), proved by the p. 2 chain
S0–S6, in the author's order:

> Cho n ∈ ℕ, n ≥ 3. Nếu phương trình xⁿ + yⁿ = zⁿ (1) có nghiệm nguyên
> khác không thì bao giờ cũng tồn tại nghiệm nguyên x = u, y = v, z = t
> sao cho (u, v) = (u, t) = (v, t) = 1.

Assembly of the verified steps: S0+S1 (`L1_reduce_coprime`), S2+S3
(`L1_step_S2_S3`), S4 (`L1_step_S4`), S5 (`L1_step_S5`), S6
(`L1_step_S6`). -/
theorem L1_bo_de_1 {n : ℕ} (hn : 3 ≤ n) {u₀ v₀ t₀ : ℤ}
    (hu₀ : u₀ ≠ 0) (hv₀ : v₀ ≠ 0) (ht₀ : t₀ ≠ 0)
    (hsol : u₀ ^ n + v₀ ^ n = t₀ ^ n) :
    ∃ u v t : ℤ, u ≠ 0 ∧ v ≠ 0 ∧ t ≠ 0 ∧ u ^ n + v ^ n = t ^ n ∧
      Int.gcd u v = 1 ∧ Int.gcd u t = 1 ∧ Int.gcd v t = 1 := by
  -- S0 + S1: divide the solution by its common gcd d = (u₀,v₀,t₀)
  obtain ⟨u, v, t, hu, hv, ht, hcop, _, _, _, hsol'⟩ :=
    L1_reduce_coprime hn hu₀ hv₀ ht₀ hsol
  have hn0 : n ≠ 0 := by omega
  -- S2 + S3 + S4: d′ = (u,v) satisfies d′ⁿ ∣ tⁿ, hence d′ ∣ t
  have hdvd_t : ((Int.gcd u v : ℕ) : ℤ) ∣ t :=
    L1_step_S4 hn0 (L1_step_S2_S3 hsol')
  -- S5: d′ divides all of u, v, t while (u,v,t) = 1, so d′ = 1
  have h_uv : Int.gcd u v = 1 :=
    L1_step_S5 (d := Int.gcd u v) (Int.gcd_dvd_left u v) (Int.gcd_dvd_right u v)
      hdvd_t hcop
  -- S6: same for the pairs (u,t) and (v,t)
  obtain ⟨h_ut, h_vt⟩ := L1_step_S6 hn0 hsol' hcop
  exact ⟨u, v, t, hu, hv, ht, hsol', h_uv, h_ut, h_vt⟩

#print axioms L1.L1_reduce_coprime
#print axioms L1.L1_step_S2_S3
#print axioms L1.L1_step_S4
#print axioms L1.L1_step_S5
#print axioms L1.L1_step_S6
#print axioms L1.L1_bo_de_1

end L1
