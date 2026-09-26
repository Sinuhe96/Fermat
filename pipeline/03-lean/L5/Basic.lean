import Mathlib

/-!
# Lemma 5 (bổ đề 5) — the author's proof, steps S0–S18

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 1, lemma 5 of section A;
  * proof: p. 2–3, section "5. Chứng minh bổ đề 5".

The literal Vietnamese transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L5-01.yml` (`source_text`, `author_steps`).
One named declaration per author step (English paraphrase):

  S0     hypotheses: n an odd prime; u, v ∈ ℤ with (u,v) = 1; A := Σ (−1)^i
         u^{n−1−i} v^i                                   -> carried by the steps
  S1     definition of A                                -> `L5.A`
  S2     u^n + v^n = [(u+v)−v]^n + v^n = (u+v)·Σ_k (−1)^k C_n^k (u+v)^{n−1−k}
         v^k, i.e. u^n + v^n = (u+v)·A  (n odd: the k = n term is −v^n)
                                                        -> L5_step_S2
  S3     "mà u+v ≠ 0, nên A = Σ_k (−1)^k C_n^k (u+v)^{n−k−1} v^k"
                                                        -> L5_step_S3
  S4     A = (u+v)·Σ_{k≤n−2} (−1)^k C_n^k (u+v)^{n−k−2} v^k + n·v^{n−1}
                                                        -> L5_step_S4
  S5     (u,v) = 1 and (u+v) ⋮̸ n give (u+v, v^{n−1}) = (u+v, n) = 1, hence
         (u+v, n·v^{n−1}) = 1                           -> L5_step_S5
  S6     (A, u+v) = 1   — part a) "(đpcm)"              -> L5_step_S6
  S7     A ⋮̸ n          — part a)'s second conjunct, NOT derived in the print
         (F3: one line from S4's binomial form)         -> L5_step_S7
  S8     A = n(u+v)·A₁ + n·v^{n−1} with the author's A₁  -> L5_step_S8
  S9     n(u+v)·A₁ ⋮ n²  (⟺ n² ∣ (u+v)·B′, since n·A₁ = B′) -> L5_step_S9
  S10    n·v^{n−1} ⋮ n but ⋮̸ n² (v ⋮̸ n)                -> L5_step_S10
  S11    A ⋮ n, A ⋮̸ n² and (u+v, A) = n  — part b) "(đpcm)" -> L5_step_S11
  S12    c) case uv ⋮ n: u ⋮ n ∧ v ⋮ n, hence n² ∣ u^n + v^n -> L5_step_S12
  S13    c) case uv ⋮̸ n: FLT gives u^{n−1} ≡ v^{n−1} ≡ 1 (mod n) -> L5_step_S13
  S14    A = u^{n−1} − v·Σ_{i≤n−2}(−1)^i u^{n−2−i} v^i and the same Σ is
         (u^{n−1} − v^{n−1})/(u+v)                      -> L5_step_S14
  S15    (u+v) ⋮̸ n would give A ≡ 1 (mod n), so n ∤ u^n+v^n, contradicting
         the hypothesis: hence (u+v) ⋮ n                 -> L5_step_S15
  S16    with (u+v) ⋮ n, b)'s result gives A ⋮ n, so u^n+v^n = (u+v)·A ⋮ n²
         — part c) "(đpcm)"                             -> L5_step_S16
  S17    d): FLT gives u^{n−1} = 1 + mn with m ∈ ℕ       -> L5_step_S17
  S18    d): u^{n(n−1)} = (u^{n−1})^n = (1+mn)^n ≡ 1 (mod n²) -> L5_step_S18
  assembly: parts a) b) c) d)                            -> L5_bo_de_5

Two of the author's steps are *not* fully derived in the print and are
supplied here from his own material, with the reason recorded in the chunk
YAML's F3 watch-list (never as a new assumption):

* S7 (a)'s second conjunct `A ⋮̸ n`: from S4's binomial form one gets
  `A ≡ (u+v)^{n−1} (mod n)` because `n ∣ C_n^k` for `1 ≤ k ≤ n−1`, so
  `n ∣ A` forces `n ∣ (u+v)`, contradicting a)'s own hypothesis.
* S8's `A₁` is *rational* (`A₁ = B′/n`, with `B′` the `k ≤ n−2` part of the
  binomial form); the author's `n(u+v)·A₁ ⋮ n²` is therefore stated here as
  the integer statement `n² ∣ (u+v)·B′`, which is the same expression.
* S3's printed derivation divides by `u+v`; the same identity is proved here
  as a polynomial identity (in `ℤ[X]` with the constant `v`), which is why
  it needs no `u+v ≠ 0` side condition — the author's division is legitimate
  in part a) but not in b)–d).

Nothing here is our own mathematics: the content is the author's chain.
-/

namespace L5

/-- The author's `A = Σ_{i=0}^{n−1} (−1)^i u^{n−1−i} v^i` (S1), defined over an
arbitrary commutative ring so that S3 can use it in `ℤ[X]`. -/
def A (R : Type*) [CommRing R] (n : ℕ) (u v : R) : R :=
  ∑ i ∈ Finset.range n, (-1 : R) ^ i * u ^ (n - 1 - i) * v ^ i

/-- The author's binomial form `Σ_{k=0}^{n−1} (−1)^k C_n^k (u+v)^{n−1−k} v^k`
of S3 (the second half of his S2 sentence). -/
def B (R : Type*) [CommRing R] (n : ℕ) (u v : R) : R :=
  ∑ k ∈ Finset.range n, (-1 : R) ^ k * (n.choose k : R) * (u + v) ^ (n - 1 - k) * v ^ k

/-- The `k ≤ n−2` part of the binomial form: the `Σ` the author factors out in
S4 (`(u+v)·Σ_{k=0}^{n−2} …`), and the integer whose `n`-multiple is his
`n(u+v)·A₁` in S8/S9. -/
def B' (R : Type*) [CommRing R] (n : ℕ) (u v : R) : R :=
  ∑ k ∈ Finset.range (n - 1), (-1 : R) ^ k * (n.choose k : R) * (u + v) ^ (n - 2 - k) * v ^ k

/-- **S2** (author p. 2 §5a, first sentence).

`u^n + v^n = [(u+v)−v]^n + v^n = (u+v)·Σ_{k=0}^{n−1} (−1)^k C_n^k
(u+v)^{n−1−k} v^k`, and the same quantity is `(u+v)·A`.

Oddness of `n` is what makes the two halves true: the `k = n` term of
`[(u+v)−v]^n` is `(−1)^n v^n = −v^n` and cancels the added `+v^n`, and
likewise `(u+v)·A = u^n − (−v)^n = u^n + v^n`.

The statement keeps both halves together because the author's sentence
asserts both; the second half is the binomial expansion, the first the
geometric identification of `A`. -/
theorem L5_step_S2 {R : Type*} [CommRing R] {n : ℕ} (hn : Odd n) (u v : R) :
    (u + v) * A R n u v = u ^ n + v ^ n ∧ (u + v) * B R n u v = u ^ n + v ^ n := by
  constructor
  · -- (u+v)·A = u^n − (−v)^n: the geometric factorization of `x^n − y^n`
    have h := Commute.mul_geom_sum₂ (Commute.all (-v : R) u) n
    rw [show (-v : R) - u = -(u + v) by ring] at h
    have hsum : (∑ i ∈ Finset.range n, (-v : R) ^ i * u ^ (n - 1 - i)) = A R n u v := by
      rw [A]
      exact Finset.sum_congr rfl fun i _ => by rw [neg_pow]; ring
    rw [hsum] at h
    rw [neg_pow, hn.neg_one_pow, neg_one_mul] at h
    have h2 : -((u + v) * A R n u v) = -(u ^ n + v ^ n) := by
      rw [← neg_mul, h]
      ring
    exact neg_inj.mp h2
  · -- (u+v)·Σ_k (−1)^k C_n^k (u+v)^{n−1−k} v^k = ((u+v) − v)^n + v^n
    have h := add_pow (-v) (u + v) n
    rw [show (-v : R) + (u + v) = u by ring] at h
    rw [Finset.sum_range_succ] at h
    simp only [tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one] at h
    have hB : (u + v) * B R n u v
        = ∑ m ∈ Finset.range n, (-v) ^ m * (u + v) ^ (n - m) * (n.choose m : R) := by
      rw [B, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hpos : 0 < n - m := Nat.sub_pos_of_lt (Finset.mem_range.mp hm)
      rw [neg_pow, show n - m = (n - 1 - m) + 1 by
        rw [Nat.sub_right_comm, Nat.sub_one_add_one_eq_of_pos hpos], pow_succ]
      ring
    rw [hB, h, neg_pow, hn.neg_one_pow, neg_one_mul]
    ring

#print axioms L5.L5_step_S2

/-- **S3** (author p. 2 §5a, second sentence): `A` equals its binomial form.

The author's derivation divides by `u+v` ("mà u+v ≠ 0, nên A = …"). The
identity is a polynomial identity in `u, v` — the author's division is
legitimate in part a) (where `(u+v) ⋮̸ n` excludes `u+v = 0`) but *not* in
b)–d) — so it is proved here without dividing, in `ℤ[X]` with the constant
`v`: both sides satisfy `(X + C v)·Y = X^n + (C v)^n` by S2, and `X + C v` is
not a zero divisor, so they agree as polynomials; evaluating at `u` gives the
claim. No `u+v ≠ 0` side condition is introduced, and no author step changes
place: this is his S3, derived from his S2. -/
theorem L5_step_S3 {n : ℕ} (hn : Odd n) (u v : ℤ) : A ℤ n u v = B ℤ n u v := by
  have hA := (L5_step_S2 hn (Polynomial.X : Polynomial ℤ) (Polynomial.C v)).1
  have hB := (L5_step_S2 hn (Polynomial.X : Polynomial ℤ) (Polynomial.C v)).2
  have hzero : (Polynomial.X + Polynomial.C v) *
      (A (Polynomial ℤ) n Polynomial.X (Polynomial.C v) -
        B (Polynomial ℤ) n Polynomial.X (Polynomial.C v)) = 0 := by
    rw [mul_sub, hA, hB, sub_self]
  have hpoly : A (Polynomial ℤ) n Polynomial.X (Polynomial.C v)
      = B (Polynomial ℤ) n Polynomial.X (Polynomial.C v) := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (Polynomial.X_add_C_ne_zero v)
    · exact sub_eq_zero.mp h
  have hE := congrArg (Polynomial.eval u) hpoly
  unfold A B at hE
  rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum] at hE
  simpa [A, B] using hE

#print axioms L5.L5_step_S3

/-- **S4** (author p. 2 §5a, third sentence): split off the last summand of the
binomial form. Its `k = n−1` term is `(−1)^{n−1}·C_n^{n−1}·v^{n−1} = n·v^{n−1}`
(`n` odd kills the sign, and `C_n^{n−1} = n`). -/
theorem L5_step_S4 {n : ℕ} (hn : Odd n) (u v : ℤ) :
    A ℤ n u v = (u + v) * B' ℤ n u v + (n : ℤ) * v ^ (n - 1) := by
  have hn1 : n = (n - 1) + 1 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hpos : 0 < n := by omega
  rw [L5_step_S3 hn u v, B, B']
  rw [show Finset.range n = Finset.range ((n - 1) + 1) from congrArg Finset.range hn1,
    Finset.sum_range_succ]
  have hlast : (-1 : ℤ) ^ (n - 1) * (n.choose (n - 1) : ℤ)
      * (u + v) ^ (n - 1 - (n - 1)) * v ^ (n - 1) = (n : ℤ) * v ^ (n - 1) := by
    have hev : Even (n - 1) := by
      obtain ⟨k, hk⟩ := hn
      exact ⟨k, by omega⟩
    have h1 : (-1 : ℤ) ^ (n - 1) = 1 := Even.neg_one_pow hev
    have h2 : n.choose (n - 1) = n := by
      have h3 : n - 1 + 1 = n := Nat.sub_one_add_one_eq_of_pos hpos
      have h := Nat.choose_succ_self_right (n - 1)
      rwa [h3] at h
    rw [h1, h2, tsub_self, pow_zero, mul_one]
    ring
  have hsum : (∑ k ∈ Finset.range (n - 1),
        (-1 : ℤ) ^ k * (n.choose k : ℤ) * (u + v) ^ (n - 1 - k) * v ^ k)
      = (u + v) * ∑ k ∈ Finset.range (n - 1),
        (-1 : ℤ) ^ k * (n.choose k : ℤ) * (u + v) ^ (n - 2 - k) * v ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hklt : k < n - 1 := Finset.mem_range.mp hk
    have hexp : (n - 2 - k) + 1 = n - 1 - k := by
      have h1 : (n - 2) + 1 = n - 1 :=
        Nat.sub_one_add_one_eq_of_pos (by omega : 0 < n - 1)
      calc (n - 2 - k) + 1 = (n - 2) + 1 - k :=
            (Nat.sub_add_comm (m := 1) (by omega : k ≤ n - 2)).symm
        _ = n - 1 - k := by rw [h1]
    rw [hexp.symm, pow_succ]
    ring
  rw [hsum, hlast]

#print axioms L5.L5_step_S4

/-- Helper for S5/S13/S15/S17: for a prime `n`, `u ⋮̸ n` says `n` is coprime to
`u` — the hypothesis form FLT (`Int.ModEq.pow_card_sub_one_eq_one`,
`Int.prime_dvd_pow_sub_one`) and the `Int.gcd` shifts both consume. -/
theorem L5_gcd_eq_one_of_not_dvd {n : ℕ} (hn : Nat.Prime n) {u : ℤ}
    (hu : ¬ (n : ℤ) ∣ u) : Int.gcd u (n : ℤ) = 1 := by
  rw [Int.gcd_def]
  have hnd : ¬ n ∣ u.natAbs := fun hd => hu (Int.natCast_dvd.mpr hd)
  have hc : Nat.Coprime n u.natAbs := (Nat.Prime.coprime_iff_not_dvd hn).mpr hnd
  simpa [Int.natAbs_natCast, Nat.gcd_comm] using hc

/-- **S5** (author p. 2 §5a → p. 3 §5a): `(u,v) = 1` with `(u+v) ⋮̸ n` gives
`(u+v, v^{n−1}) = 1` and `(u+v, n) = 1`, hence `(u+v, n·v^{n−1}) = 1`.

The first factor uses his `(u,v) = 1` (a `gcd` shift), the second his
`(u+v) ⋮̸ n` together with `n` prime (a composite `n` would break it). -/
theorem L5_step_S5 {n : ℕ} (hn : Nat.Prime n) {u v : ℤ} (hcop : Int.gcd u v = 1)
    (huv : ¬ (n : ℤ) ∣ u + v) : Int.gcd (u + v) ((n : ℤ) * v ^ (n - 1)) = 1 := by
  have hgv : Int.gcd (u + v) v = 1 := by
    have h := Int.gcd_add_mul_left_left v u 1
    rw [hcop] at h
    simpa [mul_one] using h
  have hgvp : Int.gcd (u + v) (v ^ (n - 1)) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp ((Int.isCoprime_iff_gcd_eq_one.mpr hgv).pow_right)
  have hgn : Int.gcd (u + v) (n : ℤ) = 1 := L5_gcd_eq_one_of_not_dvd hn huv
  exact Int.isCoprime_iff_gcd_eq_one.mp
    ((Int.isCoprime_iff_gcd_eq_one.mpr hgn).mul_right
      (Int.isCoprime_iff_gcd_eq_one.mpr hgvp))

#print axioms L5.L5_gcd_eq_one_of_not_dvd
#print axioms L5.L5_step_S5

/-- **S6** (author p. 3 §5a, "(đpcm)"): part a)'s first conjunct `(A, u+v) = 1`.

From S4 (`A = (u+v)·B′ + n·v^{n−1}`) the `(u+v)·B′` summand shifts the gcd
away, so `(u+v, A) = (u+v, n·v^{n−1})`, which S5 evaluates to `1`. -/
theorem L5_step_S6 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v : ℤ}
    (hcop : Int.gcd u v = 1) (huv : ¬ (n : ℤ) ∣ u + v) :
    Int.gcd (u + v) (A ℤ n u v) = 1 := by
  have h4 : A ℤ n u v = (n : ℤ) * v ^ (n - 1) + (u + v) * B' ℤ n u v := by
    rw [L5_step_S4 hodd u v]
    ring
  rw [h4, Int.gcd_add_mul_left_right (m := u + v) (n := (n : ℤ) * v ^ (n - 1))
    (k := B' ℤ n u v)]
  exact L5_step_S5 hn hcop huv

#print axioms L5.L5_step_S6

/-- **S7** (author p. 1, statement a), second conjunct): `A ⋮̸ n`.

Source note (F3, recorded in `pipeline/02-chunks/chunks/L5-01.yml`): the printed
proof closes "(đpcm)" immediately after `(A, u+v) = 1` and never derives this
conjunct — his mod-`n` technique appears only in c). The one-line derivation
supplied here uses only his own material: reducing the binomial form (S3/S4)
mod `n`, the `k = 0` term is `(u+v)^{n−1}` and every term with `1 ≤ k ≤ n−1`
carries `C_n^k ⋮ n` (n prime), so `A ≡ (u+v)^{n−1} (mod n)`; hence `n ∣ A`
would give `n ∣ (u+v)^{n−1}` and then `n ∣ u+v`, contradicting a)'s
hypothesis `(u+v) ⋮̸ n`. No new assumption enters, so this stays his chain —
it is the missing step of the printed argument, not a different route. -/
theorem L5_step_S7 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v : ℤ}
    (huv : ¬ (n : ℤ) ∣ u + v) : ¬ (n : ℤ) ∣ A ℤ n u v := by
  have hn1 : n = (n - 1) + 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hEq : A ℤ n u v = (u + v) ^ (n - 1) + ∑ k ∈ Finset.range (n - 1),
      (-1 : ℤ) ^ (k + 1) * (n.choose (k + 1) : ℤ) * (u + v) ^ (n - 1 - (k + 1))
        * v ^ (k + 1) := by
    rw [L5_step_S3 hodd u v, B]
    rw [show Finset.range n = Finset.range ((n - 1) + 1) from congrArg Finset.range hn1,
      Finset.sum_range_succ']
    simp only [pow_zero, mul_one, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    ring
  have hdvd : (n : ℤ) ∣ ∑ k ∈ Finset.range (n - 1),
      (-1 : ℤ) ^ (k + 1) * (n.choose (k + 1) : ℤ) * (u + v) ^ (n - 1 - (k + 1))
        * v ^ (k + 1) := by
    refine Finset.dvd_sum fun k hk => ?_
    have hk1 : k + 1 ≠ 0 := by omega
    have hkn : k + 1 < n := by
      have hkl : k < n - 1 := Finset.mem_range.mp hk
      omega
    obtain ⟨c, hc⟩ := hn.dvd_choose_self hk1 hkn
    exact ⟨(-1 : ℤ) ^ (k + 1) * (c : ℤ) * (u + v) ^ (n - 1 - (k + 1)) * v ^ (k + 1),
      by rw [hc]; push_cast; ring⟩
  have key : (n : ℤ) ∣ A ℤ n u v - (u + v) ^ (n - 1) := by
    rw [hEq]
    convert hdvd using 1
    ring
  intro hA
  obtain ⟨c, hc⟩ := hA
  obtain ⟨d, hd⟩ := key
  refine huv (Int.Prime.dvd_pow' (k := n - 1) hn ?_)
  refine ⟨c - d, ?_⟩
  have hx : (u + v) ^ (n - 1) = A ℤ n u v - (A ℤ n u v - (u + v) ^ (n - 1)) := by ring
  rw [hx, hd, hc]
  ring

#print axioms L5.L5_step_S7

/-- The author's `A₁` (S8): the rational bracket in
`A = n(u+v)·A₁ + n·v^{n−1}`, namely
`Σ_{k=0}^{n−3} (−1)^k (C_n^k/n)(u+v)^{n−k−2}v^k − ((n−1)v^{n−2})/2`.

It is rational (its `k = 0` term divides by `n`), which is why the author's
`n(u+v)·A₁ ⋮ n²` is encoded in S9 as the integer divisibility of `(u+v)·B′`:
`n·A₁ = B′`. -/
def A1 (n : ℕ) (u v : ℚ) : ℚ :=
  (∑ k ∈ Finset.range (n - 2),
      (-1 : ℚ) ^ k * ((n.choose k : ℚ) / n) * (u + v) ^ (n - 2 - k) * v ^ k)
    - ((n : ℚ) - 1) * v ^ (n - 2) / 2

/-- **S8** (author p. 3 §5b): `A = n(u+v)·A₁ + n·v^{n−1}` with his `A₁`.

The bridge to S9 is `n·A₁ = B′`, proved here in `ℚ`. Its content is that the
printed `−((n−1)v^{n−2})/2` is the *peeled* `k = n−2` term of `B′`:
`(−1)^{n−2}C_n^{n−2}v^{n−2}/n = −(n−1)v^{n−2}/2` (n odd, `C_n^{n−2} =
C_n^2 = n(n−1)/2`). -/
theorem L5_step_S8 {n : ℕ} (hodd : Odd n) (hn3 : 3 ≤ n) (u v : ℤ) :
    (A ℤ n u v : ℚ) = (n : ℚ) * ((u : ℚ) + (v : ℚ)) * A1 n (u : ℚ) (v : ℚ)
      + (n : ℚ) * (v : ℚ) ^ (n - 1) := by
  have h4q : (A ℤ n u v : ℚ)
      = ((u : ℚ) + (v : ℚ)) * (B' ℤ n u v : ℚ) + (n : ℚ) * (v : ℚ) ^ (n - 1) := by
    rw [L5_step_S4 hodd u v]
    push_cast
    ring
  have hchoose : (n.choose (n - 2) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
    have h1 : n.choose (n - 2) = n.choose 2 := Nat.choose_symm (by omega : 2 ≤ n)
    have h2dvd : 2 ∣ n * (n - 1) := by
      have hev : Even (n - 1) := by
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k, by omega⟩
      exact dvd_mul_of_dvd_right (even_iff_two_dvd.mp hev) n
    have h2 : n * (n - 1) / 2 * 2 = n * (n - 1) := Nat.div_mul_cancel h2dvd
    have h3 : (n.choose 2 : ℚ) * 2 = (n : ℚ) * ((n : ℚ) - 1) := by
      have h := congrArg (fun t : ℕ => (t : ℚ)) h2
      rw [← Nat.choose_two_right] at h
      push_cast at h
      rw [Nat.cast_sub (by omega : 1 ≤ n)] at h
      push_cast at h
      linarith
    rw [h1, eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)]
    exact h3
  have hpeel : (B' ℤ n u v : ℚ)
      = (∑ k ∈ Finset.range (n - 2),
          (-1 : ℚ) ^ k * (n.choose k : ℚ) * ((u : ℚ) + v) ^ (n - 2 - k) * (v : ℚ) ^ k)
        - ((n : ℚ) * ((n : ℚ) - 1) / 2) * (v : ℚ) ^ (n - 2) := by
    rw [B']
    push_cast
    rw [show Finset.range (n - 1) = Finset.range ((n - 2) + 1) from
        congrArg Finset.range
          (Nat.sub_one_add_one_eq_of_pos (by omega : 0 < n - 1)).symm,
      Finset.sum_range_succ]
    rw [tsub_self, pow_zero, mul_one]
    rw [show (-1 : ℚ) ^ (n - 2) = -1 from by
      obtain ⟨k, hk⟩ := hodd
      exact Odd.neg_one_pow ⟨k - 1, by omega⟩]
    rw [hchoose]
    ring
  have hnq : (n : ℚ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hS : (n : ℚ) * (∑ k ∈ Finset.range (n - 2),
        (-1 : ℚ) ^ k * ((n.choose k : ℚ) / n) * ((u : ℚ) + v) ^ (n - 2 - k)
          * (v : ℚ) ^ k)
      = ∑ k ∈ Finset.range (n - 2),
        (-1 : ℚ) ^ k * (n.choose k : ℚ) * ((u : ℚ) + v) ^ (n - 2 - k) * (v : ℚ) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  have hT : (n : ℚ) * (((n : ℚ) - 1) * (v : ℚ) ^ (n - 2) / 2)
      = ((n : ℚ) * ((n : ℚ) - 1) / 2) * (v : ℚ) ^ (n - 2) := by ring
  have hkey : (n : ℚ) * A1 n (u : ℚ) (v : ℚ) = (B' ℤ n u v : ℚ) := by
    rw [hpeel, A1, mul_sub, hS, hT]
  rw [h4q, ← hkey]
  ring

#print axioms L5.L5_step_S8

/-- **S9** (author p. 3 §5b): his `n(u+v)·A₁ ⋮ n²`, encoded as the integer
divisibility `n² ∣ (u+v)·B′` — the same expression, since `n·A₁ = B′` (S8).

Why it holds: in `B′ = Σ_{k=0}^{n−2}(−1)^kC_n^k(u+v)^{n−2−k}v^k` the `k = 0`
term is `(u+v)^{n−2}`, divisible by `n` because `n ⋮ u+v` and `n ≥ 3`, and
every term with `1 ≤ k ≤ n−2` carries `C_n^k ⋮ n` (n prime) — exactly the
author's reason for exhibiting the `C_n^k/n` inside `A₁`. With `n ⋮ u+v`, the
product `(u+v)·B′` is then divisible by `n²`. -/
theorem L5_step_S9 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v : ℤ}
    (hw : (n : ℤ) ∣ u + v) : (n : ℤ) ^ 2 ∣ (u + v) * B' ℤ n u v := by
  have hn2 : n - 2 ≠ 0 := by
    have h2 := hn.two_le
    obtain ⟨k, hk⟩ := hodd
    omega
  have hB : (n : ℤ) ∣ B' ℤ n u v := by
    rw [B']
    refine Finset.dvd_sum fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp only [pow_zero, mul_one, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
      exact dvd_pow hw hn2
    · have hklt : k < n - 1 := Finset.mem_range.mp hk
      obtain ⟨c, hc⟩ := hn.dvd_choose_self (by omega : k ≠ 0) (by omega : k < n)
      exact ⟨(-1 : ℤ) ^ k * (c : ℤ) * (u + v) ^ (n - 2 - k) * v ^ k,
        by rw [hc]; push_cast; ring⟩
  rw [pow_two]
  exact mul_dvd_mul hw hB

#print axioms L5.L5_step_S9

/-- **S10** (author p. 3 §5b): `n·v^{n−1} ⋮ n` but `⋮̸ n²` because `v ⋮̸ n`
(n prime) — his parenthetical "(do v ⋮̸ n)". -/
theorem L5_step_S10 {n : ℕ} (hn : Nat.Prime n) {v : ℤ} (hv : ¬ (n : ℤ) ∣ v) :
    ¬ (n : ℤ) ^ 2 ∣ (n : ℤ) * v ^ (n - 1) := by
  intro h
  obtain ⟨c, hc⟩ := h
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have h1 : (n : ℤ) ∣ v ^ (n - 1) := by
    have h2 : (n : ℤ) * v ^ (n - 1) = (n : ℤ) * ((n : ℤ) * c) := by
      rw [hc]
      ring
    exact ⟨c, mul_left_cancel₀ hn0 h2⟩
  exact hv (Int.Prime.dvd_pow' (k := n - 1) hn h1)

#print axioms L5.L5_step_S10

/-- **S11** (author p. 3 §5b, "(đpcm)"): part b)'s three conclusions.

`A = (u+v)·B′ + n·v^{n−1}` with S9 gives `A ⋮ n`; if `n²` divided `A` it would
divide the difference `n·v^{n−1}`, contradicting S10 — whose hypothesis
`v ⋮̸ n` is derived here from `(u,v) = 1` together with `n ⋮ u+v` (if `n` divided
both `u` and `v`, it would divide `(u,v) = 1`). Finally
`(u+v, A) = (u+v, n·v^{n−1}) = n`: the `(u+v)·B′` summand shifts the gcd away,
`n` divides both arguments, and the remaining cofactor is coprime to `v^{n−1}`
because `(u+v, v) = (u, v) = 1`. -/
theorem L5_step_S11 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v : ℤ}
    (hcop : Int.gcd u v = 1) (hw : (n : ℤ) ∣ u + v) :
    (n : ℤ) ∣ A ℤ n u v ∧ ¬ (n : ℤ) ^ 2 ∣ A ℤ n u v ∧
      Int.gcd (u + v) (A ℤ n u v) = n := by
  have h4 : A ℤ n u v = (n : ℤ) * v ^ (n - 1) + (u + v) * B' ℤ n u v := by
    rw [L5_step_S4 hodd u v]
    ring
  have h9 : (n : ℤ) ^ 2 ∣ (u + v) * B' ℤ n u v := L5_step_S9 hn hodd hw
  have hnv : ¬ (n : ℤ) ∣ v := by
    intro hv
    have hu : (n : ℤ) ∣ u := by
      have h : u = (u + v) - v := by ring
      rw [h]
      exact dvd_sub hw hv
    have hg : (n : ℤ) ∣ ((Int.gcd u v : ℕ) : ℤ) := Int.dvd_coe_gcd hu hv
    have h1 : n ∣ Int.gcd u v := Int.natCast_dvd_natCast.mp hg
    rw [hcop] at h1
    exact hn.ne_one (Nat.dvd_one.mp h1)
  have hn2 : (n : ℤ) ∣ (n : ℤ) ^ 2 := ⟨(n : ℤ), by ring⟩
  have hgv : Int.gcd (u + v) v = 1 := by
    have h := Int.gcd_add_mul_left_left v u 1
    rw [hcop] at h
    simpa [mul_one] using h
  refine ⟨?_, ?_, ?_⟩
  · rw [h4]
    exact dvd_add (dvd_mul_right _ _) (dvd_trans hn2 h9)
  · intro h
    have hsub : (n : ℤ) ^ 2 ∣ (n : ℤ) * v ^ (n - 1) := by
      have h' := dvd_sub h h9
      rw [h4] at h'
      convert h' using 1
      ring
    exact L5_step_S10 hn hnv hsub
  · have hgvp : Int.gcd (u + v) (v ^ (n - 1)) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp ((Int.isCoprime_iff_gcd_eq_one.mpr hgv).pow_right)
    obtain ⟨k, hk⟩ := hw
    have hgk : Int.gcd k v = 1 := by
      have hdv : Int.gcd ((n : ℤ) * k) v = 1 := by rw [← hk]; exact hgv
      have h1 : ((Int.gcd k v : ℕ) : ℤ) ∣ ((Int.gcd ((n : ℤ) * k) v : ℕ) : ℤ) :=
        Int.dvd_coe_gcd (dvd_mul_of_dvd_right (Int.gcd_dvd_left k v) (n : ℤ))
          (Int.gcd_dvd_right k v)
      rw [hdv] at h1
      exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp (by simpa using h1))
    have hgkp : Int.gcd k (v ^ (n - 1)) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp ((Int.isCoprime_iff_gcd_eq_one.mpr hgk).pow_right)
    rw [h4, Int.gcd_add_mul_left_right (m := u + v) (n := (n : ℤ) * v ^ (n - 1))
      (k := B' ℤ n u v), hk, Int.gcd_mul_left, Int.natAbs_natCast, hgkp, mul_one]

#print axioms L5.L5_step_S11

/-- **S12** (author p. 3 §5c, branch 1: "nếu uv ⋮ n"): then `u ⋮ n` and
`v ⋮ n` (n prime), so `u^n + v^n ⋮ n²` — c) is immediate in this case.

The author writes "nếu uv ⋮ n thì u ⋮ n và v ⋮ n, do đó u^n + v^n ⋮ n²"; here
the hypothesis `u^n + v^n ⋮ n` supplies the second coordinate: `n ∣ u^n` forces
`n ∣ v^n`, hence `n ∣ v` (n prime), and symmetrically. -/
theorem L5_step_S12 {n : ℕ} (hn : Nat.Prime n) {u v : ℤ} (huv : (n : ℤ) ∣ u * v)
    (hsol : (n : ℤ) ∣ u ^ n + v ^ n) : (n : ℤ) ^ 2 ∣ u ^ n + v ^ n := by
  have h2 : 2 ≤ n := hn.two_le
  have hn2 : (n : ℤ) ^ 2 ∣ (n : ℤ) ^ n := by
    refine ⟨(n : ℤ) ^ (n - 2), ?_⟩
    rw [← pow_add, show 2 + (n - 2) = n by omega]
  have key : ∀ x y : ℤ, (n : ℤ) ∣ x → (n : ℤ) ∣ y → (n : ℤ) ^ 2 ∣ x ^ n + y ^ n := by
    intro x y hx hy
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    rw [mul_pow, mul_pow]
    exact dvd_add (dvd_mul_of_dvd_left hn2 _) (dvd_mul_of_dvd_left hn2 _)
  have hother : ∀ x y : ℤ, (n : ℤ) ∣ y → (n : ℤ) ∣ x ^ n + y ^ n → (n : ℤ) ∣ x := by
    intro x y hy hxy
    have h : (n : ℤ) ∣ x ^ n := by
      have h' := dvd_sub hxy (dvd_pow hy hn.ne_zero)
      convert h' using 1
      ring
    exact Int.Prime.dvd_pow' (k := n) hn h
  rcases Int.Prime.dvd_mul' hn huv with hu | hv
  · exact key u v hu (hother v u hu (by rwa [add_comm] at hsol))
  · exact key u v (hother u v hv hsol) hv

#print axioms L5.L5_step_S12

/-- **S13** (author p. 3 §5c, branch 2): with `uv ⋮̸ n` both `u ⋮̸ n` and
`v ⋮̸ n`, so FLT mod `n` gives `u^{n−1} ≡ v^{n−1} ≡ 1 (mod n)` — exactly his
"u^{n−1} ≡ v^{n−1} ≡ 1 (mod n)", stated as the congruence of the two powers. -/
theorem L5_step_S13 {n : ℕ} (hn : Nat.Prime n) {u v : ℤ} (hu : ¬ (n : ℤ) ∣ u)
    (hv : ¬ (n : ℤ) ∣ v) : u ^ (n - 1) ≡ v ^ (n - 1) [ZMOD (n : ℤ)] := by
  have hcu : IsCoprime u (n : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (L5_gcd_eq_one_of_not_dvd hn hu)
  have hcv : IsCoprime v (n : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (L5_gcd_eq_one_of_not_dvd hn hv)
  exact (Int.ModEq.pow_card_sub_one_eq_one hn hcu).trans
    (Int.ModEq.pow_card_sub_one_eq_one hn hcv).symm

#print axioms L5.L5_step_S13

/-- **S14** (author p. 3 §5c, branch 2): `A = u^{n−1} − v·Σ_{i≤n−2}(−1)^i
u^{n−2−i}v^i`, and that same `Σ` is `(u^{n−1} − v^{n−1})/(u+v)` — the quotient
the author writes, legitimate in this branch because `(u+v) ⋮̸ n` makes
`u+v ≠ 0`. Both halves are stated without dividing: the second is
`(u+v)·A(n−1) = u^{n−1} − v^{n−1}`, a case of S2's geometric identity with the
even exponent `n−1` (so `(−v)^{n−1} = v^{n−1}`). -/
theorem L5_step_S14 {n : ℕ} (hodd : Odd n) (u v : ℤ) :
    A ℤ n u v = u ^ (n - 1) - v * A ℤ (n - 1) u v ∧
      (u + v) * A ℤ (n - 1) u v = u ^ (n - 1) - v ^ (n - 1) := by
  have hn1 : n = (n - 1) + 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hev : Even (n - 1) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  constructor
  · rw [A, A]
    rw [show Finset.range n = Finset.range ((n - 1) + 1) from congrArg Finset.range hn1,
      Finset.sum_range_succ']
    have h0 : (-1 : ℤ) ^ 0 * u ^ (n - 1 - 0) * v ^ 0 = u ^ (n - 1) := by simp
    rw [h0]
    have hs : (∑ i ∈ Finset.range (n - 1),
          (-1 : ℤ) ^ (i + 1) * u ^ (n - 1 - (i + 1)) * v ^ (i + 1))
        = -v * ∑ i ∈ Finset.range (n - 1), (-1 : ℤ) ^ i * u ^ (n - 1 - 1 - i) * v ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hexp : n - 1 - (i + 1) = n - 1 - 1 - i :=
        (Nat.sub_succ' (n - 1) i).trans (Nat.sub_right_comm (n - 1) i 1)
      rw [hexp, pow_succ, pow_succ]
      ring
    rw [hs]
    ring
  · have h := Commute.mul_geom_sum₂ (Commute.all (-v : ℤ) u) (n - 1)
    rw [show (-v : ℤ) - u = -(u + v) by ring] at h
    have hsum : (∑ i ∈ Finset.range (n - 1), (-v : ℤ) ^ i * u ^ (n - 1 - 1 - i))
        = A ℤ (n - 1) u v := by
      rw [A]
      exact Finset.sum_congr rfl fun i _ => by rw [neg_pow]; ring
    rw [hsum] at h
    rw [neg_pow, Even.neg_one_pow hev, one_mul] at h
    have h2 : -((u + v) * A ℤ (n - 1) u v) = -(u ^ (n - 1) - v ^ (n - 1)) := by
      rw [← neg_mul, h]
      ring
    exact neg_inj.mp h2

#print axioms L5.L5_step_S14

/-- Helper for S15: `(x : ZMod n) = 0 ↔ n ⋮ x` — the bridge between the
divisibility hypotheses of c) and the field `ZMod n` in which its branch 2 is
argued. -/
theorem L5_zmod_intCast_eq_zero_iff {n : ℕ} [NeZero n] (x : ℤ) :
    ((x : ZMod n) = 0) ↔ (n : ℤ) ∣ x :=
  CharP.intCast_eq_zero_iff (ZMod n) n x

/-- **S15** (author p. 3 §5c, branch 2: `uv ⋮̸ n`): then `(u+v) ⋮ n`.

His argument, transcribed into the field `ZMod n` (where `(u+v) ⋮̸ n` makes
`u+v` nonzero and `uv ⋮̸ n` makes both `u`, `v` nonzero, so `u+v` is invertible
and `u^{n−1} = v^{n−1} = 1` by FLT): S14's geometric identity
`(u+v)·A(n−1) = u^{n−1} − v^{n−1}` forces `A(n−1) = 0`; S14's recursion
`A(n) = u^{n−1} − v·A(n−1)` then gives `A(n) = 1`; but the hypothesis
`u^n + v^n ⋮ n` and S2's `(u+v)·A(n) = u^n + v^n` make a product of two
nonzero elements of `ZMod n` vanish — contradiction. -/
theorem L5_step_S15 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v : ℤ}
    (huv : ¬ (n : ℤ) ∣ u * v) (hsol : (n : ℤ) ∣ u ^ n + v ^ n) :
    (n : ℤ) ∣ u + v := by
  by_contra hw
  have : Fact (Nat.Prime n) := ⟨hn⟩
  have : NeZero n := ⟨hn.ne_zero⟩
  have hu : ¬ (n : ℤ) ∣ u := fun h => huv (dvd_mul_of_dvd_left h v)
  have hv : ¬ (n : ℤ) ∣ v := fun h => huv (dvd_mul_of_dvd_right h u)
  have hU0 : (u : ZMod n) ≠ 0 := fun h => hu ((L5_zmod_intCast_eq_zero_iff u).mp h)
  have hV0 : (v : ZMod n) ≠ 0 := fun h => hv ((L5_zmod_intCast_eq_zero_iff v).mp h)
  have hUV0 : (u : ZMod n) + (v : ZMod n) ≠ 0 := by
    intro h
    exact hw ((L5_zmod_intCast_eq_zero_iff (u + v)).mp (by simpa using h))
  have hU1 : (u : ZMod n) ^ (n - 1) = 1 := ZMod.pow_card_sub_one_eq_one hU0
  have hV1 : (v : ZMod n) ^ (n - 1) = 1 := ZMod.pow_card_sub_one_eq_one hV0
  have hA1 : (((A ℤ (n - 1) u v) : ℤ) : ZMod n) = 0 := by
    have h' := congrArg (fun t : ℤ => (t : ZMod n)) (L5_step_S14 hodd u v).2
    push_cast at h'
    rw [hU1, hV1, sub_self, mul_eq_zero] at h'
    rcases h' with h' | h'
    · exact absurd h' hUV0
    · exact h'
  have hAn : (((A ℤ n u v) : ℤ) : ZMod n) ≠ 0 := by
    have hE : (((A ℤ n u v) : ℤ) : ZMod n) = 1 := by
      have h' := congrArg (fun t : ℤ => (t : ZMod n)) (L5_step_S14 hodd u v).1
      push_cast at h'
      rw [h', hA1, mul_zero, hU1]
      ring
    rw [hE]
    exact one_ne_zero
  have hzero : (u : ZMod n) ^ n + (v : ZMod n) ^ n = 0 := by
    have h := (L5_zmod_intCast_eq_zero_iff (u ^ n + v ^ n)).mpr hsol
    push_cast at h
    exact h
  have hprod : ((u : ZMod n) + (v : ZMod n)) * (((A ℤ n u v) : ℤ) : ZMod n) = 0 := by
    have h' := congrArg (fun t : ℤ => (t : ZMod n)) (L5_step_S2 hodd u v).1
    push_cast at h'
    rw [h', hzero]
  exact mul_ne_zero hUV0 hAn hprod

#print axioms L5.L5_zmod_intCast_eq_zero_iff
#print axioms L5.L5_step_S15

/-- **S16** (author p. 3 §5c, "(đpcm)" for branch 2): with `(u+v) ⋮ n`, part
b)'s `A ⋮ n` — which needs only S4 and `u+v ⋮ n`, *not* b)'s coprimality, as
his parenthetical "theo một kết quả chứng minh ở b)" requires — gives
`u^n + v^n = (u+v)·A ⋮ n²`. -/
theorem L5_step_S16 {n : ℕ} (hodd : Odd n) {u v : ℤ} (hw : (n : ℤ) ∣ u + v) :
    (n : ℤ) ^ 2 ∣ u ^ n + v ^ n := by
  have h4 : A ℤ n u v = (n : ℤ) * v ^ (n - 1) + (u + v) * B' ℤ n u v := by
    rw [L5_step_S4 hodd u v]
    ring
  have hA : (n : ℤ) ∣ A ℤ n u v := by
    rw [h4]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hw _)
  have h2 : (u + v) * A ℤ n u v = u ^ n + v ^ n := (L5_step_S2 hodd u v).1
  rw [← h2, pow_two]
  exact mul_dvd_mul hw hA

#print axioms L5.L5_step_S16

/-- **S17** (author p. 3 §5d): FLT gives `u^{n−1} = 1 + mn`, and `m` may be
taken in `ℕ` — non-negative because `u ⋮̸ n` makes `u ≠ 0` while `n − 1` is
even, so `u^{n−1} = (u^j)² > 0` and hence `≥ 1`. -/
theorem L5_step_S17 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u : ℤ}
    (hu : ¬ (n : ℤ) ∣ u) : ∃ m : ℕ, u ^ (n - 1) = 1 + (m : ℤ) * n := by
  have hcop : IsCoprime u (n : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (L5_gcd_eq_one_of_not_dvd hn hu)
  obtain ⟨k, hk⟩ := Int.prime_dvd_pow_sub_one hn hcop
  have hu0 : u ≠ 0 := by
    intro h0
    exact hu (by rw [h0]; exact dvd_zero _)
  have hge : 1 ≤ u ^ (n - 1) := by
    obtain ⟨j, hj⟩ := hodd
    have he : n - 1 = j + j := by omega
    rw [he, pow_add]
    have hpos : 0 < u ^ j * u ^ j := mul_self_pos.mpr (pow_ne_zero j hu0)
    omega
  have hk0 : 0 ≤ k := by
    have hnpos : 0 < (n : ℤ) := by exact_mod_cast hn.pos
    have h : 0 ≤ k * (n : ℤ) := by
      rw [mul_comm k (n : ℤ), ← hk]
      omega
    exact nonneg_of_mul_nonneg_left h hnpos
  refine ⟨k.toNat, ?_⟩
  rw [Int.toNat_of_nonneg hk0, mul_comm]
  omega

#print axioms L5.L5_step_S17

/-- Helper for S18: `n² ∣ (m·n)^j` for `2 ≤ j`. -/
theorem L5_nsq_dvd_mul_pow {n m : ℤ} {j : ℕ} (hj : 2 ≤ j) : n ^ 2 ∣ (m * n) ^ j := by
  have hsplit : n ^ j = n ^ 2 * n ^ (j - 2) := by
    rw [← pow_add, show 2 + (j - 2) = j by omega]
  refine ⟨m ^ j * n ^ (j - 2), ?_⟩
  rw [mul_pow, hsplit]
  ring

/-- **S18** (author p. 3 §5d): `u^{n(n−1)} = (u^{n−1})^n = (1+mn)^n ≡ 1
(mod n²)` — the binomial expansion of `(1+mn)^n`, whose `j ≥ 1` terms all
carry `n²` (the `j = 1` term is `m·n·n`, and the `j ≥ 2` terms carry `n^j`). -/
theorem L5_step_S18 {n : ℕ} {u m : ℤ} (hm : u ^ (n - 1) = 1 + m * n) :
    u ^ (n * (n - 1)) ≡ 1 [ZMOD (n : ℤ) ^ 2] := by
  have hpow : u ^ (n * (n - 1)) = (1 + m * n) ^ n := by
    rw [show n * (n - 1) = (n - 1) * n by ring, pow_mul, hm]
  have h' : (n : ℤ) ^ 2 ∣ (1 + m * n) ^ n - 1 := by
    have h := add_pow (m * n) (1 : ℤ) n
    rw [show m * n + 1 = 1 + m * n by ring] at h
    have h1 : (1 + m * n) ^ n - 1
        = ∑ j ∈ Finset.range n,
            (m * n) ^ (j + 1) * 1 ^ (n - (j + 1)) * (n.choose (j + 1) : ℤ) := by
      rw [h, Finset.sum_range_succ']
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_pow, Nat.sub_zero]
      ring
    rw [h1]
    refine Finset.dvd_sum fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      have hcn : (n.choose 1 : ℤ) = (n : ℤ) := by rw [Nat.choose_one_right]
      rw [hcn]
      simp only [one_pow, mul_one]
      exact ⟨m, by ring⟩
    · have hj2 : 2 ≤ j + 1 := by omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (L5_nsq_dvd_mul_pow hj2) _) _
  rw [Int.modEq_iff_dvd, hpow]
  simpa only [neg_sub] using dvd_neg.mpr h'

#print axioms L5.L5_nsq_dvd_mul_pow
#print axioms L5.L5_step_S18

/-- Assembly: bổ đề 5, parts a)–d), chaining the step theorems in the author's
order (`(đpcm)`).

* a) `(u+v) ⋮̸ n` ⟹ `(A, u+v) = 1` and `A ⋮̸ n` (S6, S7);
* b) `(u+v) ⋮ n` ⟹ `A ⋮ n`, `A ⋮̸ n²` and `(u+v, A) = n` (S11);
* c) `u^n + v^n ⋮ n` ⟹ `u^n + v^n ⋮ n²`, split on `uv ⋮ n` (S12) and `uv ⋮̸ n`
  (S13 → S14 → S15 → S16);
* d) `u ⋮̸ n` ⟹ `u^{n(n−1)} ≡ 1 (mod n²)` (S17 → S18). -/
theorem L5_bo_de_5 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v : ℤ}
    (hcop : Int.gcd u v = 1) :
    (¬ (n : ℤ) ∣ u + v →
        Int.gcd (u + v) (A ℤ n u v) = 1 ∧ ¬ (n : ℤ) ∣ A ℤ n u v) ∧
      ((n : ℤ) ∣ u + v →
        (n : ℤ) ∣ A ℤ n u v ∧ ¬ (n : ℤ) ^ 2 ∣ A ℤ n u v ∧
          Int.gcd (u + v) (A ℤ n u v) = n) ∧
      ((n : ℤ) ∣ u ^ n + v ^ n → (n : ℤ) ^ 2 ∣ u ^ n + v ^ n) ∧
      (¬ (n : ℤ) ∣ u → u ^ (n * (n - 1)) ≡ 1 [ZMOD (n : ℤ) ^ 2]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact ⟨L5_step_S6 hn hodd hcop h, L5_step_S7 hn hodd h⟩
  · intro h
    exact L5_step_S11 hn hodd hcop h
  · intro h
    by_cases huvn : (n : ℤ) ∣ u * v
    · exact L5_step_S12 hn huvn h
    · exact L5_step_S16 hodd (L5_step_S15 hn hodd huvn h)
  · intro h
    obtain ⟨m, hm⟩ := L5_step_S17 hn hodd h
    exact L5_step_S18 hm

#print axioms L5.L5_bo_de_5

end L5
