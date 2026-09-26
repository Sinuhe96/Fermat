import Mathlib
import L3.Basic
import L4.Basic
import L5.Basic

/-!
# Lemma 6 (bổ đề 6) — the author's proof, steps S0–S27

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 1, lemma 6 of section A;
  * proof: p. 3 §6 – p. 4 §6.2.1 (case tree 6.1 / 6.2 / 6.2.1).

The literal Vietnamese transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L6-01.yml` (`source_text`, `author_steps`).
One named declaration per author step (English paraphrase):

  S0        hypotheses (carried by every step theorem below)
  S1        (1) re-read as u^n + v^n = t^n (3)              -> inside S2
  S2        (4), (5), (6): the three factorisations         -> L6_step_S2
  S3        case 6.1 (t ⋮̸ n): (u+v), (t−v), (t−u) ⋮̸ n     -> L6_step_S3
  S4        bổ đề 5 a) at (u,v), (t,−v), (t,−u)            -> L6_step_S4
  S5        bổ đề 3 at (4), (5), (6)                        -> L6_step_S5
  S6        (a,b) = (a,c) = (c,b) = 1                       -> L6_step_S6
  S7        c'^n − 1 = Σ_{k≥1} … + [(u+v)^{n−1} − 1]        -> L6_step_S7
  S8        C_n^k ⋮ n and FLT ⇒ c'^n − 1 ⋮ n                -> L6_step_S8
  S9 + S10  c' = 1 + n k₃, a' = 1 + n k₁, b' = 1 + n k₂     -> L6_step_S9_S10
  S11       t^n − u − v = c^n[(1+nk₃)^n − 1] ⋮ n²           -> L6_step_S11
  S12       2(u+v−t) ⋮ n² (three-term identity) ⇒ u+v−t ⋮ n² -> L6_step_S12
  S13       u+v−t = c(c^{n−1}−c') = a(a'−a^{n−1}) = b(b'−b^{n−1})
            = n^s a b c k, s ≥ 2, (k,a)=(k,b)=(k,c)=1, k ⋮̸ n -> L6_step_S13
  S14       6.1 conclusion (h = c^n)                        -> L6_step_S14
  S15       6.2: t ⋮ n ⇒ (u+v) ⋮ n                          -> L6_step_S15
  S16       bổ đề 5 b) + bổ đề 4 at (4)                     -> L6_step_S16
  S17       (5''): t^n − u − v ⋮ n²                         -> L6_step_S17
  S18       6.2: (t−v), (t−u) ⋮̸ n; bổ đề 5 a)               -> L6_step_S18
  S19       bổ đề 3 twice ⇒ (5'), (6')                      -> L6_step_S19
  S20+S21+S22  "Lập luận như 6.1": (5''), (6''), the
            three-term identity ⇒ (u+v−t) ⋮ n² in 6.2       -> L6_step_S20_S22
  S23       the 6.2 factorisation of u+v−t, s ≥ 2           -> L6_step_S23
  S24       6.2 conclusion (h = n^{ns−1}c^n)                -> L6_step_S24
  S25+S26   6.2.1: k = 0 forces |a| = |b| = 1, t ∈ {−2,0,2},
            absurd ("vô lý")                              -> L6_step_S25_S26
  assembly  the lemma's conclusion (6.1 ∨ 6.2)              -> L6_bo_de_6

## Encoding decisions (the print's notation, made explicit)

* The author's (5) and (6) carry the *non-alternating* sums
  `Σ_{i=0}^{n−1} t^{n−1−i}v^i` and `Σ_{i=0}^{n−1} t^{n−1−i}u^i` (the
  difference factorisations of `t^n − v^n = u^n` resp. `t^n − u^n = v^n`).
  Because `L5.A R n x y = Σ_i (−1)^i x^{n−1−i}y^i`, that sum is exactly
  `L5.A ℤ n t (−v)`, and bổ đề 5's part a) applies to it with the pair
  `(t, −v)` whose "sum" `t + (−v) = t − v` is what S3 bounds. Same for
  `L5.A ℤ n t (−u)` at (6). No extra definition or rewrite is introduced:
  the paper's two sums are literal instances of the already-verified `A`.
* The print's `k ≠ 0` ("nếu k ≠ 0", and the conclusion's "bốn số nguyên
  khác không") is *derived*: §6.2.1's own argument applied to 6.1 closes
  the `k = 0` case (chunk YAML F1 note 7), and in 6.2 the case is §6.2.1
  itself. Both derivations are marked `S13`/`S25+S26` below.
* Three printed step justifications are loose but the steps are the
  author's own and true from his hypotheses; each is recorded at the step
  that supplies the derivation (F3, never a new assumption):
  (i) S15's "từ (4) suy ra (u+v) ⋮ n" — the route is t ⋮ n ⇒ n ∣ t^n =
  u^n+v^n and FLT mod n (his own technique from S8) ⇒ n ∣ u+v;
  (ii) S9's intermediate "(c'^{n−1} − 1) ⋮ n" is FLT at c' (needs c' ⋮̸ n);
  (iii) S13's "s ≥ 2" is the n-adic maximality argument (his S12 gives
  n² ∣ u+v−t and n ∤ abc).
-/

namespace L6

/-- `Int.gcd a (-b) = Int.gcd a b`: the author's pair `(t, −v)` has the same
gcd as `(t, v)`, which is the coprimality hypothesis the print supplies. -/
lemma L6_gcd_neg_right (a b : ℤ) : Int.gcd a (-b) = Int.gcd a b := by
  rw [Int.gcd_def, Int.gcd_def, Int.natAbs_neg]

/-- `Int.gcd (-a) b = Int.gcd a b`, the left version of the above. -/
lemma L6_gcd_neg_left (a b : ℤ) : Int.gcd (-a) b = Int.gcd a b := by
  rw [Int.gcd_def, Int.gcd_def, Int.natAbs_neg]

/-- **S1 + S2** (author p. 3 §6, the three displayed identities).

From the solution `u^n + v^n = t^n` (3):

* (4) `(u+v)·Σ(−1)^i u^{n−1−i}v^i = t^n` — the sum factorisation, i.e.
  bổ đề 5's `L5_step_S2` at `(u,v)`;
* (5) `(t−v)·Σ t^{n−1−i}v^i = u^n` — the difference factorisation of
  `t^n − v^n = u^n`, encoded as `L5_step_S2` at `(t, −v)` (see the header
  note: `Σ t^{n−1−i}v^i = A ℤ n t (−v)`);
* (6) `(t−u)·Σ t^{n−1−i}u^i = v^n` — likewise at `(t, −u)`.

The author's (4) needs `n` odd (the `k = n` term of `[(u+v)−v]^n` is
`(−1)^n v^n = −v^n`); (5)/(6) are the difference factorisations and hold
for all `n`, but they are stated here as instances of the same `A` so that
bổ đề 5's part a) applies to them verbatim. -/
theorem L6_step_S2 {n : ℕ} (hodd : Odd n) {u v t : ℤ} (hsol : u ^ n + v ^ n = t ^ n) :
    (u + v) * L5.A ℤ n u v = t ^ n ∧
      (t - v) * L5.A ℤ n t (-v) = u ^ n ∧
      (t - u) * L5.A ℤ n t (-u) = v ^ n := by
  refine ⟨?_, ?_, ?_⟩
  · exact (L5.L5_step_S2 hodd u v).1.trans hsol
  · have h := (L5.L5_step_S2 hodd t (-v)).1
    rw [show t + -v = t - v by ring, Odd.neg_pow hodd v] at h
    exact h.trans (by omega)
  · have h := (L5.L5_step_S2 hodd t (-u)).1
    rw [show t + -u = t - u by ring, Odd.neg_pow hodd u] at h
    exact h.trans (by omega)

#print axioms L6.L6_gcd_neg_right
#print axioms L6.L6_gcd_neg_left
#print axioms L6.L6_step_S2

/-- **S3** (author p. 3 §6.1, first sentence of the case `t ⋮̸ n`):
`(u+v) ⋮̸ n`, `(t−v) ⋮̸ n` and `(t−u) ⋮̸ n`.

Suppose `n ∣ u+v`; then (4) gives `n ∣ t^n`, so `n ∣ t` (`n` prime) against
the case hypothesis. Suppose `n ∣ t−v`; then (5) gives `n ∣ u^n`, so `n ∣ u`,
so `n ∣ uv`, against the lemma's `uv ⋮̸ n`; and (6) the same for `t−u`.
The print also cites `(u,v) = (u,t) = (v,t) = 1` in this sentence, but the
contradiction only consumes the lemma's own `uv ⋮̸ n` and primality of `n`. -/
theorem L6_step_S3 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t : ℤ}
    (hsol : u ^ n + v ^ n = t ^ n) (huvn : ¬ (n : ℤ) ∣ u * v) (ht : ¬ (n : ℤ) ∣ t) :
    ¬ (n : ℤ) ∣ u + v ∧ ¬ (n : ℤ) ∣ t - v ∧ ¬ (n : ℤ) ∣ t - u := by
  obtain ⟨h4, h5, h6⟩ := L6_step_S2 hodd hsol
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hd : (n : ℤ) ∣ t ^ n := by
      have : (n : ℤ) ∣ (u + v) * L5.A ℤ n u v := dvd_mul_of_dvd_left h _
      rwa [h4] at this
    exact ht (Int.Prime.dvd_pow' (k := n) hn hd)
  · intro h
    have hd : (n : ℤ) ∣ u ^ n := by
      have : (n : ℤ) ∣ (t - v) * L5.A ℤ n t (-v) := dvd_mul_of_dvd_left h _
      rwa [h5] at this
    exact huvn (dvd_mul_of_dvd_left (Int.Prime.dvd_pow' (k := n) hn hd) v)
  · intro h
    have hd : (n : ℤ) ∣ v ^ n := by
      have : (n : ℤ) ∣ (t - u) * L5.A ℤ n t (-u) := dvd_mul_of_dvd_left h _
      rwa [h6] at this
    exact huvn (dvd_mul_of_dvd_right (Int.Prime.dvd_pow' (k := n) hn hd) u)

#print axioms L6.L6_step_S3

/-- **S4** (author p. 3 §6.1): bổ đề 5 a) at the three pairs `(u,v)`, `(t,−v)`
and `(t,−u)`.

Part a) needs the pair coprime and *its* sum `⋮̸ n`. For `(t,−v)` the sum is
`t + (−v) = t − v` (S3) and `(t,−v) = 1` is the lemma's `(v,t) = 1`
(`Int.gcd t (-v) = Int.gcd t v = Int.gcd v t`), and likewise for `(t,−u)`
with `(u,t) = 1`. The print's three equalities `(·, Σ) = 1` are the three
`gcd` conclusions; its three `Σ ⋮̸ n` are the second conjuncts. -/
theorem L6_step_S4 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t : ℤ}
    (huv : Int.gcd u v = 1) (hut : Int.gcd u t = 1) (hvt : Int.gcd v t = 1)
    (hnuv : ¬ (n : ℤ) ∣ u + v) (hntv : ¬ (n : ℤ) ∣ t - v) (hntu : ¬ (n : ℤ) ∣ t - u) :
    Int.gcd (u + v) (L5.A ℤ n u v) = 1 ∧ ¬ (n : ℤ) ∣ L5.A ℤ n u v ∧
      Int.gcd (t - v) (L5.A ℤ n t (-v)) = 1 ∧ ¬ (n : ℤ) ∣ L5.A ℤ n t (-v) ∧
      Int.gcd (t - u) (L5.A ℤ n t (-u)) = 1 ∧ ¬ (n : ℤ) ∣ L5.A ℤ n t (-u) := by
  have hcop_tv : Int.gcd t (-v) = 1 := by
    rw [L6_gcd_neg_right, Int.gcd_comm]
    exact hvt
  have hcop_tu : Int.gcd t (-u) = 1 := by
    rw [L6_gcd_neg_right, Int.gcd_comm]
    exact hut
  obtain ⟨h1a, h1b⟩ := (L5.L5_bo_de_5 hn hodd huv).1 hnuv
  obtain ⟨h2a, h2b⟩ := (L5.L5_bo_de_5 hn hodd hcop_tv).1 (by simpa [sub_eq_add_neg] using hntv)
  obtain ⟨h3a, h3b⟩ := (L5.L5_bo_de_5 hn hodd hcop_tu).1 (by simpa [sub_eq_add_neg] using hntu)
  exact ⟨h1a, h1b, by simpa [sub_eq_add_neg] using h2a, h2b,
    by simpa [sub_eq_add_neg] using h3a, h3b⟩

#print axioms L6.L6_step_S4

/-- **S5** (author p. 3 §6.1): bổ đề 3 applied to (4), (5) and (6).

Each pair `(u+v, Σ(−1)^i u^{n−1−i}v^i)`, `(t−v, Σ t^{n−1−i}v^i)`,
`(t−u, Σ t^{n−1−i}u^i)` is a product of two nonzero coprime integers equal to
a perfect `n`-th power (`t^n`, `u^n`, `v^n`), so bổ đề 3's hypotheses hold —
`n` odd positive, gcd `1` from S4, both factors nonzero because the product
is `t^n`/`u^n`/`v^n ≠ 0`. The print's `c ⋮̸ n, c' ⋮̸ n` (and the analogous
pairs) follow from S3/S4: `n ∣ c` would force `n ∣ c^n = u+v`, and `n ∣ c'`
would force `n ∣ c'^n = Σ`, both excluded.

The print's second factors are the non-alternating sums `Σ t^{n−1−i}v^i`,
`Σ t^{n−1−i}u^i`, which are `L5.A ℤ n t (−v)` and `L5.A ℤ n t (−u)` (header
note) — the same objects S4 applied bổ đề 5 a) to. -/
theorem L6_step_S5 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t : ℤ}
    (hu : u ≠ 0) (hv : v ≠ 0) (ht : t ≠ 0)
    (hsol : u ^ n + v ^ n = t ^ n)
    (huv : Int.gcd u v = 1) (hut : Int.gcd u t = 1) (hvt : Int.gcd v t = 1)
    (huvn : ¬ (n : ℤ) ∣ u * v) (hcase : ¬ (n : ℤ) ∣ t) :
    (∃ c c' : ℤ, c ≠ 0 ∧ c' ≠ 0 ∧ Int.gcd c c' = 1 ∧ t = c * c' ∧
        u + v = c ^ n ∧ L5.A ℤ n u v = c' ^ n ∧ ¬ (n : ℤ) ∣ c ∧ ¬ (n : ℤ) ∣ c') ∧
      (∃ b b' : ℤ, b ≠ 0 ∧ b' ≠ 0 ∧ Int.gcd b b' = 1 ∧ u = b * b' ∧
        t - v = b ^ n ∧ L5.A ℤ n t (-v) = b' ^ n ∧ ¬ (n : ℤ) ∣ b ∧ ¬ (n : ℤ) ∣ b') ∧
      (∃ a a' : ℤ, a ≠ 0 ∧ a' ≠ 0 ∧ Int.gcd a a' = 1 ∧ v = a * a' ∧
        t - u = a ^ n ∧ L5.A ℤ n t (-u) = a' ^ n ∧ ¬ (n : ℤ) ∣ a ∧ ¬ (n : ℤ) ∣ a') := by
  obtain ⟨h4, h5, h6⟩ := L6_step_S2 hodd hsol
  obtain ⟨hnuv, hntv, hntu⟩ := L6_step_S3 hn hodd hsol huvn hcase
  obtain ⟨hc4, hA4, hc5, hA5, hc6, hA6⟩ := L6_step_S4 hn hodd huv hut hvt hnuv hntv hntu
  have htne : t ^ n ≠ 0 := pow_ne_zero n ht
  have hune : u ^ n ≠ 0 := pow_ne_zero n hu
  have hvne : v ^ n ≠ 0 := pow_ne_zero n hv
  have hwne : u + v ≠ 0 := fun h => htne (by rw [← h4, h, zero_mul])
  have hAne : L5.A ℤ n u v ≠ 0 := fun h => htne (by rw [← h4, h, mul_zero])
  have htvne : t - v ≠ 0 := fun h => hune (by rw [← h5, h, zero_mul])
  have hA5ne : L5.A ℤ n t (-v) ≠ 0 := fun h => hune (by rw [← h5, h, mul_zero])
  have htune : t - u ≠ 0 := fun h => hvne (by rw [← h6, h, zero_mul])
  have hA6ne : L5.A ℤ n t (-u) ≠ 0 := fun h => hvne (by rw [← h6, h, mul_zero])
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, c', hc0, hc'0, hgcd_cc', ht_cc', huv_c, hA_c'⟩ :=
      L3.L3_bo_de_3 hodd hn.pos hwne hAne ht h4 hc4
    exact ⟨c, c', hc0, hc'0, hgcd_cc', ht_cc', huv_c, hA_c',
      fun h => hnuv (by rw [huv_c]; exact dvd_pow h hn.ne_zero),
      fun h => hA4 (by rw [hA_c']; exact dvd_pow h hn.ne_zero)⟩
  · obtain ⟨b, b', hb0, hb'0, hgcd_bb', hu_bb', htv_b, hA_b'⟩ :=
      L3.L3_bo_de_3 hodd hn.pos htvne hA5ne hu h5 hc5
    exact ⟨b, b', hb0, hb'0, hgcd_bb', hu_bb', htv_b, hA_b',
      fun h => hntv (by rw [htv_b]; exact dvd_pow h hn.ne_zero),
      fun h => hA5 (by rw [hA_b']; exact dvd_pow h hn.ne_zero)⟩
  · obtain ⟨a, a', ha0, ha'0, hgcd_aa', hv_aa', htu_a, hA_a'⟩ :=
      L3.L3_bo_de_3 hodd hn.pos htune hA6ne hv h6 hc6
    exact ⟨a, a', ha0, ha'0, hgcd_aa', hv_aa', htu_a, hA_a',
      fun h => hntu (by rw [htu_a]; exact dvd_pow h hn.ne_zero),
      fun h => hA6 (by rw [hA_a']; exact dvd_pow h hn.ne_zero)⟩

#print axioms L6.L6_step_S5

/-- `(x,y) = 1` from `x ∣ p`, `y ∣ q` and `(p,q) = 1`: any common divisor of
`x` and `y` divides both `p` and `q`, hence divides `(p,q) = 1`. -/
lemma L6_gcd_eq_one_of_dvd {x y p q : ℤ} (hx : x ∣ p) (hy : y ∣ q)
    (h : Int.gcd p q = 1) : Int.gcd x y = 1 := by
  refine Nat.dvd_one.mp ?_
  have h1 : ((Int.gcd x y : ℕ) : ℤ) ∣ p := (Int.gcd_dvd_left x y).trans hx
  have h2 : ((Int.gcd x y : ℕ) : ℤ) ∣ q := (Int.gcd_dvd_right x y).trans hy
  have h3 : Int.gcd x y ∣ Int.gcd p q := Int.dvd_gcd h1 h2
  rwa [h] at h3

/-- **S6** (author p. 3 §6.1): `(a,b) = (a,c) = (c,b) = 1`.

The print's justification is its parenthetical
`(b·b', a·a') = (b·b', c·c') = (a·a', c·c') = 1` — the lemma's
`(u,v) = (u,t) = (v,t) = 1` transported through S5's `u = b·b'`,
`v = a·a'`, `t = c·c'`: `a ∣ v` and `b ∣ u`, so a common divisor of `a, b`
divides the coprime pair `(v,u)`; likewise for the other two. -/
theorem L6_step_S6 {u v t a a' b b' c c' : ℤ}
    (hu : u = b * b') (hv : v = a * a') (ht : t = c * c')
    (huv : Int.gcd u v = 1) (hut : Int.gcd u t = 1) (hvt : Int.gcd v t = 1) :
    Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd c b = 1 := by
  have ha_v : a ∣ v := by rw [hv]; exact dvd_mul_right a a'
  have hb_u : b ∣ u := by rw [hu]; exact dvd_mul_right b b'
  have hc_t : c ∣ t := by rw [ht]; exact dvd_mul_right c c'
  have hvu : Int.gcd v u = 1 := by rw [Int.gcd_comm]; exact huv
  have htu : Int.gcd t u = 1 := by rw [Int.gcd_comm]; exact hut
  exact ⟨L6_gcd_eq_one_of_dvd ha_v hb_u hvu,
    L6_gcd_eq_one_of_dvd ha_v hc_t hvt,
    L6_gcd_eq_one_of_dvd hc_t hb_u htu⟩

#print axioms L6.L6_gcd_eq_one_of_dvd
#print axioms L6.L6_step_S6

/-- **S7** (author p. 3 §6.1): the identity behind `c'^n − 1 ⋮ n`.

Expanding `c'^n = Σ_{i=0}^{n−1}(−1)^i u^{n−1−i}v^i` through bổ đề 5's binomial
form (his S3 there: `u = (u+v) − v`) and peeling the `k = 0` summand
`(u+v)^{n−1}` gives the print's displayed identity. Purely an identity of
integers — it already carries the author's `u+v = c^n` implicitly, since the
binomial form is written in `u+v`. -/
theorem L6_step_S7 {n : ℕ} (hodd : Odd n) {u v c' : ℤ} (hA : L5.A ℤ n u v = c' ^ n) :
    c' ^ n - 1 = (∑ k ∈ Finset.range (n - 1),
        (-1 : ℤ) ^ (k + 1) * (n.choose (k + 1) : ℤ) * (u + v) ^ (n - 1 - (k + 1)) * v ^ (k + 1))
      + ((u + v) ^ (n - 1) - 1) := by
  have hn1 : n = (n - 1) + 1 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  rw [← hA, L5.L5_step_S3 hodd u v, L5.B]
  rw [show Finset.range n = Finset.range ((n - 1) + 1) from congrArg Finset.range hn1,
    Finset.sum_range_succ']
  simp only [pow_zero, mul_one, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  ring

#print axioms L6.L6_step_S7

/-- **S8** (author p. 4 §6.1, first sentence): `n ∣ c'^n − 1`.

In S7's display every summand carries `C_n^{k}` with `1 ≤ k ≤ n−1`, and `n`
prime gives `n ∣ C_n^{k}` (the print's "C_n^k ⋮ n"); the bracket
`(u+v)^{n−1} − 1` is `⋮ n` by Fermat's little theorem (the print cites
"định lý nhỏ Fermat"), which needs `n ∤ u+v` — S3's first conjunct. -/
theorem L6_step_S8 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v c' : ℤ}
    (huv : ¬ (n : ℤ) ∣ u + v) (hA : L5.A ℤ n u v = c' ^ n) :
    (n : ℤ) ∣ c' ^ n - 1 := by
  rw [L6_step_S7 hodd hA]
  refine dvd_add ?_ ?_
  · refine Finset.dvd_sum fun k hk => ?_
    have hk1 : k + 1 ≠ 0 := by omega
    have hkn : k + 1 < n := by
      have hkl : k < n - 1 := Finset.mem_range.mp hk
      omega
    obtain ⟨c, hc⟩ := hn.dvd_choose_self hk1 hkn
    exact ⟨(-1 : ℤ) ^ (k + 1) * (c : ℤ) * (u + v) ^ (n - 1 - (k + 1)) * v ^ (k + 1),
      by rw [hc]; push_cast; ring⟩
  · exact Int.prime_dvd_pow_sub_one hn
      (Int.isCoprime_iff_gcd_eq_one.mpr (L5.L5_gcd_eq_one_of_not_dvd hn huv))

#print axioms L6.L6_step_S8

/-- The single-instance content of S9/S10, parameterized over the pair.

If `n ∤ x+y` and `z^n = A ℤ n x y` with `n ∤ z` (`n` an odd prime), then
`z ≡ 1 (mod n)`. This is the author's argument for `(u,v)` (his S9), written
once so that S10's two "chứng minh tương tự" instances at `(t,−v)` and
`(t,−u)` are the same proof — not a different route.

* `n ∣ z^n − 1`: S8.
* Fermat at `z` (needs `n ∤ z`) gives `n ∣ z^{n−1} − 1` — this is the print's
  intermediate "mà c' ⋮̸ n nên (c'^{n−1} − 1) ⋮ n".
* subtracting: `n ∣ z^{n−1}(z − 1)`; Euclid with `(n, z) = 1` gives
  `n ∣ z − 1`, i.e. `z = 1 + n k`. -/
lemma L6_one_add_n_mul_of {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {x y z : ℤ}
    (hxy : ¬ (n : ℤ) ∣ x + y) (hA : L5.A ℤ n x y = z ^ n) (hz : ¬ (n : ℤ) ∣ z) :
    ∃ k : ℤ, z = 1 + (n : ℤ) * k := by
  have h1 : (n : ℤ) ∣ z ^ n - 1 := L6_step_S8 hn hodd hxy hA
  have hsplit : z ^ (n - 1) * z = z ^ n := by
    rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos hn.pos]
  have h2 : (n : ℤ) ∣ z ^ (n - 1) - 1 :=
    Int.prime_dvd_pow_sub_one hn
      (Int.isCoprime_iff_gcd_eq_one.mpr (L5.L5_gcd_eq_one_of_not_dvd hn hz))
  have h3 : (n : ℤ) ∣ z ^ (n - 1) * (z - 1) := by
    have hsub : (n : ℤ) ∣ (z ^ n - 1) - (z ^ (n - 1) - 1) := dvd_sub h1 h2
    convert hsub using 1
    rw [← hsplit]
    ring
  have h4 : (n : ℤ) ∣ z - 1 := by
    refine Int.dvd_of_dvd_mul_left_of_gcd_one (by rw [mul_comm]; exact h3) ?_
    have hcop : IsCoprime (n : ℤ) z :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by
        rw [Int.gcd_comm]
        exact L5.L5_gcd_eq_one_of_not_dvd hn hz)
    exact Int.isCoprime_iff_gcd_eq_one.mp (hcop.pow_right)
  obtain ⟨k, hk⟩ := h4
  exact ⟨k, by omega⟩

#print axioms L6.L6_one_add_n_mul_of

/-- **S9** (author p. 4 §6.1): `c' = 1 + n k₃` — `L6_one_add_n_mul_of` at the
pair `(u,v)`, whose `A` is `c'^n` (S5's (4')). -/
theorem L6_step_S9 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v c' : ℤ}
    (huv : ¬ (n : ℤ) ∣ u + v) (hA : L5.A ℤ n u v = c' ^ n) (hc' : ¬ (n : ℤ) ∣ c') :
    ∃ k : ℤ, c' = 1 + (n : ℤ) * k :=
  L6_one_add_n_mul_of hn hodd huv hA hc'

#print axioms L6.L6_step_S9

/-- **S10** (author p. 4 §6.1): "Chứng minh tương tự ta cũng có `a' = 1 + n k₁`,
`b' = 1 + n k₂`" — the same instance at (5') and (6'), i.e. at the pairs
`(t,−v)` (whose `A` is `b'^n`) and `(t,−u)` (whose `A` is `a'^n`). Their
`(t−v) ⋮̸ n`, `(t−u) ⋮̸ n` are S3 and `b' ⋮̸ n`, `a' ⋮̸ n` are S5's. -/
theorem L6_step_S10 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {t v u b' a' : ℤ}
    (hntv : ¬ (n : ℤ) ∣ t - v) (hntu : ¬ (n : ℤ) ∣ t - u)
    (hA5 : L5.A ℤ n t (-v) = b' ^ n) (hA6 : L5.A ℤ n t (-u) = a' ^ n)
    (hnb' : ¬ (n : ℤ) ∣ b') (hna' : ¬ (n : ℤ) ∣ a') :
    (∃ k : ℤ, b' = 1 + (n : ℤ) * k) ∧ (∃ k : ℤ, a' = 1 + (n : ℤ) * k) :=
  ⟨L6_one_add_n_mul_of hn hodd (by simpa [sub_eq_add_neg] using hntv) hA5 hnb',
    L6_one_add_n_mul_of hn hodd (by simpa [sub_eq_add_neg] using hntu) hA6 hna'⟩

#print axioms L6.L6_step_S10

/-- `n² ∣ (1 + n·k)^n − 1` for every `k` — the binomial expansion behind S11
and S12. The `j = 1` term of the expansion is `n·(nk) = n²k`, and every
`j ≥ 2` term carries `n^j` hence `n²`. No hypothesis on `n` is needed (as for
bổ đề 5's own `L5_nsq_dvd_mul_pow`; in 6.1 `n ≥ 3` anyway). -/
lemma L6_nsq_dvd_one_add_mul_pow (n : ℕ) (k : ℤ) :
    (n : ℤ) ^ 2 ∣ (1 + (n : ℤ) * k) ^ n - 1 := by
  have key : (n : ℤ) ^ 2 ∣ (1 + k * (n : ℤ)) ^ n - 1 := by
    have h := add_pow (k * (n : ℤ)) (1 : ℤ) n
    rw [show k * (n : ℤ) + 1 = 1 + k * (n : ℤ) by ring] at h
    have h1 : (1 + k * (n : ℤ)) ^ n - 1
        = ∑ j ∈ Finset.range n,
            (k * (n : ℤ)) ^ (j + 1) * 1 ^ (n - (j + 1)) * (n.choose (j + 1) : ℤ) := by
      rw [h, Finset.sum_range_succ']
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_pow, Nat.sub_zero]
      ring
    rw [h1]
    refine Finset.dvd_sum fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      have hcn : (n.choose 1 : ℤ) = (n : ℤ) := by rw [Nat.choose_one_right]
      rw [hcn]
      simp only [Nat.zero_add, pow_one, one_pow, mul_one]
      exact ⟨k, by ring⟩
    · have hj2 : 2 ≤ j + 1 := by omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (L5.L5_nsq_dvd_mul_pow hj2) _) _
  simpa only [show (1 + (n : ℤ) * k : ℤ) = 1 + k * (n : ℤ) by ring] using key

#print axioms L6.L6_nsq_dvd_one_add_mul_pow

/-- `((n:ℤ)^2, 2) = 1` for odd `n`: the halving step of S12/S22 needs `2`
invertible modulo `n²`. -/
lemma L6_isCoprime_sq_two {n : ℕ} (hodd : Odd n) : IsCoprime ((n : ℤ) ^ 2) 2 := by
  rw [Int.isCoprime_iff_nat_coprime]
  have h2dvd : ¬ (2 : ℕ) ∣ n := by
    intro h
    obtain ⟨j, hj⟩ := hodd
    obtain ⟨j', hj'⟩ := h
    omega
  have hcop : Nat.Coprime n 2 := by
    rw [Nat.coprime_comm]
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr h2dvd
  simpa [Int.natAbs_pow, Int.natAbs_natCast] using hcop.pow 2 1

#print axioms L6.L6_isCoprime_sq_two

/-- **S11** (author p. 4 §6.1): `t^n − u − v = c^n[(1 + n k₃)^n − 1] ⋮ n²`.

`t = c·c'`, `u + v = c^n` (both S5) and `c' = 1 + n k₃` (S9): the identity is
`(c·c')^n − c^n = c^n(c'^n − 1)`, and a multiple of `n²` times `c^n` is a
multiple of `n²`. -/
theorem L6_step_S11 {n : ℕ} {u v t c c' k : ℤ} (huv : u + v = c ^ n) (ht : t = c * c')
    (hk : c' = 1 + (n : ℤ) * k) :
    t ^ n - u - v = c ^ n * ((1 + (n : ℤ) * k) ^ n - 1) ∧ (n : ℤ) ^ 2 ∣ t ^ n - u - v := by
  have hX : t ^ n - u - v = c ^ n * ((1 + (n : ℤ) * k) ^ n - 1) := by
    have h1 : t ^ n - u - v = (c * c') ^ n - (u + v) := by rw [ht]; ring
    rw [h1, huv, mul_pow, hk]
    ring
  refine ⟨hX, ?_⟩
  rw [hX]
  exact dvd_mul_of_dvd_right (L6_nsq_dvd_one_add_mul_pow n k) (c ^ n)

#print axioms L6.L6_step_S11

/-- **S12** (author p. 4 §6.1): `(u^n − t + v) ⋮ n²`, `(v^n − t + u) ⋮ n²`,
their three-term combination equals `2(u+v−t)`, hence `(u+v−t) ⋮ n²`.

`u^n − t + v = u^n − (t−v) = b^n(b'^n − 1)` with `b' = 1 + n k₂` (S5, S10),
so S11's computation with `b` in place of `c` gives `⋮ n²`; same for
`v^n − t + u` with `a'`; and `(t^n − u − v) ⋮ n²` is S11 itself (the print
re-uses it in this very sentence). The three together are exactly `2(u+v−t)`
by `u^n + v^n = t^n`, and the halving is legitimate because `2` is coprime to
`n²` (n odd) — the print's implicit "chia 2". -/
theorem L6_step_S12 {n : ℕ} (hodd : Odd n) {u v t a a' b b' k₁ k₂ : ℤ}
    (hsol : u ^ n + v ^ n = t ^ n)
    (hu : u = b * b') (htv : t - v = b ^ n) (hk₂ : b' = 1 + (n : ℤ) * k₂)
    (hv : v = a * a') (htu : t - u = a ^ n) (hk₁ : a' = 1 + (n : ℤ) * k₁)
    (h11 : (n : ℤ) ^ 2 ∣ t ^ n - u - v) :
    (n : ℤ) ^ 2 ∣ u ^ n - t + v ∧ (n : ℤ) ^ 2 ∣ v ^ n - t + u ∧
      (u ^ n - t + v) + (v ^ n - t + u) - (t ^ n - u - v) = 2 * (u + v - t) ∧
      (n : ℤ) ^ 2 ∣ u + v - t := by
  have h1 : (n : ℤ) ^ 2 ∣ u ^ n - t + v := by
    have he : u ^ n - t + v = b ^ n * ((1 + (n : ℤ) * k₂) ^ n - 1) := by
      have h : u ^ n - t + v = (b * b') ^ n - b ^ n := by rw [hu, ← htv]; ring
      rw [h, mul_pow, hk₂]
      ring
    rw [he]
    exact dvd_mul_of_dvd_right (L6_nsq_dvd_one_add_mul_pow n k₂) (b ^ n)
  have h2 : (n : ℤ) ^ 2 ∣ v ^ n - t + u := by
    have he : v ^ n - t + u = a ^ n * ((1 + (n : ℤ) * k₁) ^ n - 1) := by
      have h : v ^ n - t + u = (a * a') ^ n - a ^ n := by rw [hv, ← htu]; ring
      rw [h, mul_pow, hk₁]
      ring
    rw [he]
    exact dvd_mul_of_dvd_right (L6_nsq_dvd_one_add_mul_pow n k₁) (a ^ n)
  have hid : (u ^ n - t + v) + (v ^ n - t + u) - (t ^ n - u - v) = 2 * (u + v - t) := by
    rw [← hsol]
    ring
  have h3 : (n : ℤ) ^ 2 ∣ 2 * (u + v - t) := by
    rw [← hid]
    exact dvd_sub (dvd_add h1 h2) h11
  exact ⟨h1, h2, hid, (L6_isCoprime_sq_two hodd).dvd_of_dvd_mul_left h3⟩

#print axioms L6.L6_step_S12

/-- `(k,a) = 1` from `k ∣ A` and `(A,a) = 1`. -/
lemma L6_gcd_eq_one_of_dvd_left {k A a : ℤ} (hk : k ∣ A) (hA : Int.gcd A a = 1) :
    Int.gcd k a = 1 := by
  refine Nat.dvd_one.mp ?_
  have h1 : ((Int.gcd k a : ℕ) : ℤ) ∣ A := (Int.gcd_dvd_left k a).trans hk
  have h2 : ((Int.gcd k a : ℕ) : ℤ) ∣ a := Int.gcd_dvd_right k a
  have h3 : Int.gcd k a ∣ Int.gcd A a := Int.dvd_gcd h1 h2
  rwa [hA] at h3

/-- `(x' − x^{n−1}, x) = 1` from `(x,x') = 1` (`n ≥ 2`): `x^{n−1}` is a
multiple of `x`, so the gcd is that of `x'` and `x` (the author's
`(a,a') = (b,b') = 1` at the quantities `X/a = a' − a^{n−1}`). -/
lemma L6_gcd_sub_pow_eq_one {n : ℕ} (hn2 : 2 ≤ n) {x x' : ℤ} (h : Int.gcd x x' = 1) :
    Int.gcd (x' - x ^ (n - 1)) x = 1 := by
  have hsplit : x ^ (n - 1) = x * x ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']
  have hshift : Int.gcd (x' - x ^ (n - 1)) x = Int.gcd x' x := by
    have hh := Int.gcd_add_mul_left_left x x' (-(x ^ (n - 2)))
    rw [show x' + x * (-(x ^ (n - 2))) = x' - x ^ (n - 1) by rw [hsplit]; ring] at hh
    exact hh
  rw [hshift, Int.gcd_comm]
  exact h

/-- `(x^{n−1} − x', x) = 1` from `(x,x') = 1` — the sign-reversed version of
`L6_gcd_sub_pow_eq_one` (the author's `(c,c') = 1` at `X/c = c^{n−1} − c'`). -/
lemma L6_gcd_pow_sub_eq_one {n : ℕ} (hn2 : 2 ≤ n) {x x' : ℤ} (h : Int.gcd x x' = 1) :
    Int.gcd (x ^ (n - 1) - x') x = 1 := by
  have hsplit : x ^ (n - 1) = x * x ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']
  have hshift : Int.gcd (x ^ (n - 1) - x') x = Int.gcd (-x') x := by
    have hh := Int.gcd_add_mul_right_left x (-x') (x ^ (n - 2))
    rw [show -x' + x ^ (n - 2) * x = x ^ (n - 1) - x' by rw [hsplit]; ring] at hh
    exact hh
  rw [hshift, L6_gcd_neg_left, Int.gcd_comm]
  exact h

/-- `(x, x^{n−1}) = |x|` for `n ≥ 2` (a multiple of `x` shares its gcd with
`x`); the step that turns `a' = a^{n−1}` and `(a,a') = 1` into `|a| = 1`. -/
lemma L6_gcd_self_pow {n : ℕ} (hn : 2 ≤ n) (x : ℤ) : Int.gcd x (x ^ (n - 1)) = x.natAbs := by
  have hsplit : x ^ (n - 1) = x * x ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']
  have hone : Int.gcd 1 (x ^ (n - 2)) = 1 := by
    rw [Int.gcd_def, Int.natAbs_one]
    exact Nat.gcd_one_left _
  have hmain := Int.gcd_mul_left x 1 (x ^ (n - 2))
  rw [mul_one x, hone, Nat.mul_one, ← hsplit] at hmain
  exact hmain

#print axioms L6.L6_gcd_eq_one_of_dvd_left
#print axioms L6.L6_gcd_sub_pow_eq_one
#print axioms L6.L6_gcd_pow_sub_eq_one
#print axioms L6.L6_gcd_self_pow

/-- **S13** (author p. 4 §6.1, last sentence): the parametrisation
`u+v−t = c(c^{n−1} − c') = a(a' − a^{n−1}) = b(b' − b^{n−1}) = n^s a b c k`
with `s ≥ 2`, `k ≠ 0`, `(k,a) = (k,b) = (k,c) = 1`, `k ⋮̸ n`.

The three displayed expressions are this step's hypotheses `hXa`/`hXb`/`hXc`
(to be read with `X = u+v−t`). `a b c ∣ X`: each of `a, b, c` divides `X`
(each divides one of the three equal expressions) and they are pairwise
coprime (S6). `gcd(abc, n) = 1` since `n ∤ a, b, c` (S5). Taking `s` the
*maximal* `n`-power in `X` — legitimate since `X ≠ 0` — S12's `n² ∣ X` gives
`s ≥ 2`, and `abc ∣ X` with `gcd(abc,n) = 1` gives `abc ∣ X/n^s`, i.e.
`X/n^s = a b c k`; then `k ≠ 0` (`X ≠ 0`), `n ∤ k` (else `n ∣ abc k =
X/n^s`, contradicting maximality) and `(k,a) = (k,b) = (k,c) = 1` because `k`
divides `X/a = a' − a^{n−1}` (resp. `X/b`, `X/c`), which is coprime to `a`
(resp. `b`, `c`) by `(a,a') = (b,b') = (c,c') = 1`.

The print states `s ≥ 2`, `(k,a) = …`, `k ⋮̸ n` under "nếu `k ≠ 0`"; the
`k = 0` case is excluded in 6.1 by the author's own §6.2.1 argument
(`L6_zero_case`, F3 closure — chunk YAML F1 note 7), so once `hX0 : X ≠ 0` is
supplied the four properties hold unconditionally. -/
theorem L6_step_S13 {n : ℕ} (hn : Nat.Prime n) {a a' b b' c c' X : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hna : ¬ (n : ℤ) ∣ a) (hnb : ¬ (n : ℤ) ∣ b) (hnc : ¬ (n : ℤ) ∣ c)
    (hab : Int.gcd a b = 1) (hac : Int.gcd a c = 1) (hcb : Int.gcd c b = 1)
    (haa' : Int.gcd a a' = 1) (hbb' : Int.gcd b b' = 1) (hcc' : Int.gcd c c' = 1)
    (hXa : X = a * (a' - a ^ (n - 1))) (hXb : X = b * (b' - b ^ (n - 1)))
    (hXc : X = c * (c ^ (n - 1) - c'))
    (hX0 : X ≠ 0) (hnsq : (n : ℤ) ^ 2 ∣ X) :
    ∃ s : ℕ, ∃ k : ℤ, 2 ≤ s ∧ X = (n : ℤ) ^ s * (a * b * c * k) ∧ k ≠ 0 ∧
      ¬ (n : ℤ) ∣ k ∧ Int.gcd k a = 1 ∧ Int.gcd k b = 1 ∧ Int.gcd k c = 1 := by
  have hXabs : X.natAbs ≠ 0 := fun h => hX0 (Int.natAbs_eq_zero.mp h)
  obtain ⟨e, R, hR, hXR⟩ := Nat.exists_eq_pow_mul_and_not_dvd hXabs n hn.one_lt.ne'
  have hdecomp : (n : ℤ) ^ e ∣ X := by
    have h1 : ((n ^ e : ℕ) : ℤ) ∣ X := Int.natCast_dvd.mpr ⟨R, hXR⟩
    simpa only [Nat.cast_pow] using h1
  obtain ⟨r, hr⟩ := hdecomp
  have hrabs : r.natAbs = R := by
    have h := hXR
    rw [hr, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h
    exact mul_left_cancel₀ (pow_ne_zero e hn.ne_zero) h
  have hrndvd : ¬ (n : ℤ) ∣ r := fun hd => hR (hrabs ▸ (Int.natCast_dvd.mp hd))
  have hr0 : r ≠ 0 := fun h => hX0 (by rw [hr, h, mul_zero])
  have h2nat : n ^ 2 ∣ n ^ e * r.natAbs := by
    rw [hrabs, ← hXR]
    exact Int.natCast_dvd.mp (by simpa only [Nat.cast_pow] using hnsq)
  have hcopR : Nat.Coprime (n ^ 2) r.natAbs := by
    have h' : Nat.Coprime n r.natAbs := by rw [hrabs]; exact (hn.coprime_iff_not_dvd).mpr hR
    simpa using h'.pow 2 1
  have he2 : 2 ≤ e :=
    (Nat.pow_dvd_pow_iff_le_right hn.one_lt).mp (hcopR.dvd_of_dvd_mul_right h2nat)
  have haX : a ∣ X := by rw [hXa]; exact dvd_mul_right a _
  have hbX : b ∣ X := by rw [hXb]; exact dvd_mul_right b _
  have hcX : c ∣ X := by rw [hXc]; exact dvd_mul_right c _
  have hcop_ab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hab
  have hcop_ac : IsCoprime a c := Int.isCoprime_iff_gcd_eq_one.mpr hac
  have habX : a * b ∣ X := hcop_ab.mul_dvd haX hbX
  have habc_cop : IsCoprime (a * b) c := IsCoprime.mul_left hcop_ac (IsCoprime.symm
    (Int.isCoprime_iff_gcd_eq_one.mpr hcb))
  have habcX : a * b * c ∣ X := habc_cop.mul_dvd habX hcX
  have hna_cop : IsCoprime (n : ℤ) a :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_comm]; exact L5.L5_gcd_eq_one_of_not_dvd hn hna)
  have hnb_cop : IsCoprime (n : ℤ) b :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_comm]; exact L5.L5_gcd_eq_one_of_not_dvd hn hnb)
  have hnc_cop : IsCoprime (n : ℤ) c :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_comm]; exact L5.L5_gcd_eq_one_of_not_dvd hn hnc)
  have hcop_n_abc : IsCoprime (n : ℤ) (a * b * c) :=
    IsCoprime.mul_right (IsCoprime.mul_right hna_cop hnb_cop) hnc_cop
  have hcop3 : IsCoprime (a * b * c) ((n : ℤ) ^ e) := (hcop_n_abc.pow_left).symm
  have habc_r : a * b * c ∣ r := by
    have h : a * b * c ∣ ((n : ℤ) ^ e) * r := by rw [← hr]; exact habcX
    exact hcop3.dvd_of_dvd_mul_left h
  obtain ⟨k, hk⟩ := habc_r
  have hk0 : k ≠ 0 := fun h => hr0 (by rw [hk, h, mul_zero])
  have hnk : ¬ (n : ℤ) ∣ k := fun h =>
    hrndvd (by rw [hk]; exact dvd_mul_of_dvd_right h (a * b * c))
  have hAa : a' - a ^ (n - 1) = (n : ℤ) ^ e * (b * (c * k)) := by
    have h : a * (a' - a ^ (n - 1)) = a * ((n : ℤ) ^ e * (b * (c * k))) := by
      rw [← hXa, hr, hk]
      ring
    exact mul_left_cancel₀ ha h
  have hA' : k ∣ a' - a ^ (n - 1) := by
    rw [hAa]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_left k c) b) ((n : ℤ) ^ e)
  have hBa : b' - b ^ (n - 1) = (n : ℤ) ^ e * (a * (c * k)) := by
    have h : b * (b' - b ^ (n - 1)) = b * ((n : ℤ) ^ e * (a * (c * k))) := by
      rw [← hXb, hr, hk]
      ring
    exact mul_left_cancel₀ hb h
  have hB' : k ∣ b' - b ^ (n - 1) := by
    rw [hBa]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_left k c) a) ((n : ℤ) ^ e)
  have hCa : c ^ (n - 1) - c' = (n : ℤ) ^ e * (a * (b * k)) := by
    have h : c * (c ^ (n - 1) - c') = c * ((n : ℤ) ^ e * (a * (b * k))) := by
      rw [← hXc, hr, hk]
      ring
    exact mul_left_cancel₀ hc h
  have hC' : k ∣ c ^ (n - 1) - c' := by
    rw [hCa]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_left k b) a) ((n : ℤ) ^ e)
  exact ⟨e, k, he2, by rw [hr, hk]; try ring, hk0, hnk,
    L6_gcd_eq_one_of_dvd_left hA' (L6_gcd_sub_pow_eq_one hn.two_le haa'),
    L6_gcd_eq_one_of_dvd_left hB' (L6_gcd_sub_pow_eq_one hn.two_le hbb'),
    L6_gcd_eq_one_of_dvd_left hC' (L6_gcd_pow_sub_eq_one hn.two_le hcc')⟩

#print axioms L6.L6_step_S13

/-- The print's §6.2.1 argument, usable in **both** cases: if `u + v − t = 0`
(i.e. `k = 0`, since `u+v−t = n^s a b c k`) then `t − u = v` and `t − v = u`,
so `a^n = a·a'`, `b^n = b·b'`; with `(a,a') = (b,b') = 1` this forces
`|a| = |a'| = |b| = |b'| = 1`, hence `u = b^n = ±1` and `v = a^n = ±1`
(`n` odd). Then `t = u + v ∈ {−2, 0, 2}` and `t^n = u^n + v^n = u + v = t`;
`t = 0` contradicts the hypothesis `t ∈ ℤ*` and `|t| = 2` contradicts `n ≥ 3`.

This is the closure of the `k = 0` case in 6.1 that the print leaves out
(F3 — chunk YAML F1 note 7), and for 6.2 it *is* the printed §6.2.1. -/
theorem L6_zero_case {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t a a' b b' : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) (hsol : u ^ n + v ^ n = t ^ n)
    (hv : v = a * a') (htu : t - u = a ^ n) (hg_aa' : Int.gcd a a' = 1)
    (hu : u = b * b') (htv : t - v = b ^ n) (hg_bb' : Int.gcd b b' = 1)
    (hX : u + v - t = 0) : False := by
  have hn3 : 3 ≤ n := by have h2 := hn.two_le; obtain ⟨j, hj⟩ := hodd; omega
  have htnu : t - u = v := by omega
  have htnv : t - v = u := by omega
  have hva : v = a ^ n := by rw [← htnu]; exact htu
  have hvb : u = b ^ n := by rw [← htnv]; exact htv
  have han : a ^ n = a * a ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
  have hbn : b ^ n = b * b ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
  have ha' : a' = a ^ (n - 1) := by
    have h : a ^ n = a * a' := by rw [← hva, hv]
    rw [han] at h
    exact (mul_left_cancel₀ ha h).symm
  have hb' : b' = b ^ (n - 1) := by
    have h : b ^ n = b * b' := by rw [← hvb, hu]
    rw [hbn] at h
    exact (mul_left_cancel₀ hb h).symm
  have ha1 : a.natAbs = 1 := by
    have h : Int.gcd a (a ^ (n - 1)) = 1 := by rw [← ha']; exact hg_aa'
    rwa [L6_gcd_self_pow hn.two_le] at h
  have hb1 : b.natAbs = 1 := by
    have h : Int.gcd b (b ^ (n - 1)) = 1 := by rw [← hb']; exact hg_bb'
    rwa [L6_gcd_self_pow hn.two_le] at h
  have ha_pm : a = 1 ∨ a = -1 := by
    have h : a.natAbs = (1 : ℤ).natAbs := by rw [Int.natAbs_one]; exact ha1
    exact Int.natAbs_eq_natAbs_iff.mp h
  have hb_pm : b = 1 ∨ b = -1 := by
    have h : b.natAbs = (1 : ℤ).natAbs := by rw [Int.natAbs_one]; exact hb1
    exact Int.natAbs_eq_natAbs_iff.mp h
  have hva' : v = a := by
    rw [hva]
    rcases ha_pm with h | h
    · rw [h, one_pow]
    · rw [h, Odd.neg_one_pow hodd]
  have hub' : u = b := by
    rw [hvb]
    rcases hb_pm with h | h
    · rw [h, one_pow]
    · rw [h, Odd.neg_one_pow hodd]
  have hu_pm : u = 1 ∨ u = -1 := by
    rcases hb_pm with h | h
    · exact Or.inl (by rw [hub', h])
    · exact Or.inr (by rw [hub', h])
  have hv_pm : v = 1 ∨ v = -1 := by
    rcases ha_pm with h | h
    · exact Or.inl (by rw [hva', h])
    · exact Or.inr (by rw [hva', h])
  rcases hu_pm with hu1 | hu1 <;> rcases hv_pm with hv1 | hv1
  · -- u = 1, v = 1: t = 2 and 2^n = 2, impossible for n ≥ 3
    have ht2 : t = 2 := by
      rw [show t = u + v by omega, hu1, hv1]
      norm_num
    have h2n : (2 : ℤ) ^ n = 2 := by
      have h := hsol
      rw [hu1, hv1, one_pow, ht2] at h
      norm_num at h
      exact h.symm
    have h2n' : (2 : ℕ) ^ n = 2 := by
      have := congrArg Int.natAbs h2n
      simpa [Int.natAbs_pow, Int.natAbs_natCast] using this
    have hle : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  · exfalso
    have ht0 : t = 0 := by
      rw [show t = u + v by omega, hu1, hv1]
      norm_num
    exact ht ht0
  · exfalso
    have ht0 : t = 0 := by
      rw [show t = u + v by omega, hu1, hv1]
      norm_num
    exact ht ht0
  · -- u = -1, v = -1: t = -2 and (−2)^n = −2, impossible for n ≥ 3
    have ht2 : t = -2 := by
      rw [show t = u + v by omega, hu1, hv1]
      norm_num
    have h2n : (2 : ℤ) ^ n = 2 := by
      have h := hsol
      rw [hu1, hv1, Odd.neg_one_pow hodd, ht2] at h
      rw [Odd.neg_pow hodd] at h
      omega
    have h2n' : (2 : ℕ) ^ n = 2 := by
      have := congrArg Int.natAbs h2n
      simpa [Int.natAbs_pow, Int.natAbs_natCast] using this
    have hle : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega

#print axioms L6.L6_zero_case

/-- **S14** (author p. 4 §6.1 end): case 6.1's conclusion,
`v = a^n + X`, `u = b^n + X`, `t = c^n − X`, `a^n + b^n = c^n − 2X` with
`X = n^s a b c k` and `h = c^n = u+v` ((4')).

Each of the first two comes from `X = b(b' − b^{n−1})` resp.
`X = a(a' − a^{n−1})` together with `u = b·b'`, `v = a·a'`; `t = c^n − X`
from `t = c·c'` and `X = c(c^{n−1} − c')`; and the last from
`a^n = v − X`, `b^n = u − X` and `u + v = c^n`. The three nonvanishing
hypotheses `a, b, c ≠ 0` (author S0) are carried in the statement for
faithfulness but are not consumed by this step's conclusion, so they are
bound as `_ha`, `_hb`, `_hc`. -/
theorem L6_step_S14 {n : ℕ} (hodd : Odd n) {u v t a a' b b' c c' k : ℤ} {s : ℕ}
    (_ha : a ≠ 0) (_hb : b ≠ 0) (_hc : c ≠ 0)
    (huv : u + v = c ^ n) (ht : t = c * c') (hu' : u = b * b') (hv' : v = a * a')
    (hXa : u + v - t = a * (a' - a ^ (n - 1)))
    (hXb : u + v - t = b * (b' - b ^ (n - 1)))
    (hXc : u + v - t = c * (c ^ (n - 1) - c'))
    (hXk : u + v - t = (n : ℤ) ^ s * (a * b * c * k)) :
    v = a ^ n + (n : ℤ) ^ s * (a * b * c * k) ∧
      u = b ^ n + (n : ℤ) ^ s * (a * b * c * k) ∧
      t = c ^ n - (n : ℤ) ^ s * (a * b * c * k) ∧
      a ^ n + b ^ n = c ^ n - 2 * ((n : ℤ) ^ s * (a * b * c * k)) := by
  have hn0 : 0 < n := by obtain ⟨j, hj⟩ := hodd; omega
  have han : a ^ n = a * a ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn0]
  have hbn : b ^ n = b * b ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn0]
  have hcn : c ^ n = c * c ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn0]
  have hub : u = b ^ n + (n : ℤ) ^ s * (a * b * c * k) := by
    have h1 : b * b' = b ^ n + (u + v - t) := by rw [hXb, hbn]; ring
    rw [hu', h1, hXk]
  have hav : v = a ^ n + (n : ℤ) ^ s * (a * b * c * k) := by
    have h1 : a * a' = a ^ n + (u + v - t) := by rw [hXa, han]; ring
    rw [hv', h1, hXk]
  have hat : t = c ^ n - (n : ℤ) ^ s * (a * b * c * k) := by
    have h1 : c * c' = c ^ n - (u + v - t) := by rw [hXc, hcn]; ring
    rw [ht, h1, hXk]
  refine ⟨hav, hub, hat, ?_⟩
  have hA : a ^ n = v - (n : ℤ) ^ s * (a * b * c * k) := by omega
  have hB : b ^ n = u - (n : ℤ) ^ s * (a * b * c * k) := by omega
  have hC : c ^ n = u + v := huv.symm
  omega

#print axioms L6.L6_step_S14

/-- **S15** (author p. 4 §6.2, first sentence): `t ⋮ n ⇒ (u+v) ⋮ n`.

The print writes "từ (4) suy ra", but (4) alone (`(u+v)·A = t^n`) does not
give it; the derivation supported by the print's hypotheses is his own FLT
technique: `n ∣ t` gives `n ∣ t^n = u^n + v^n`, and FLT in the form
`x^n ≡ x (mod n)` (`Int.ModEq.pow_prime_eq_self`, which holds *without* a
coprimality hypothesis) reduces `u^n + v^n ≡ u + v`, so `u + v ≡ 0`. This is
an F3 fill-in (recorded in the chunk notes): the author's own step, true from
his hypotheses, by the tool he uses elsewhere. The lemma's `uv ⋮̸ n` is
carried in the statement for faithfulness but is not consumed here. -/
theorem L6_step_S15 {n : ℕ} (hn : Nat.Prime n) {u v t : ℤ}
    (hsol : u ^ n + v ^ n = t ^ n) (_huvn : ¬ (n : ℤ) ∣ u * v) (ht : (n : ℤ) ∣ t) :
    (n : ℤ) ∣ u + v := by
  have h1 : (n : ℤ) ∣ u ^ n + v ^ n := by
    rw [hsol]
    exact dvd_pow ht hn.ne_zero
  have hadd : u ^ n + v ^ n ≡ u + v [ZMOD (n : ℤ)] :=
    (Int.ModEq.pow_prime_eq_self hn u).add (Int.ModEq.pow_prime_eq_self hn v)
  have hzero : u + v ≡ 0 [ZMOD (n : ℤ)] :=
    hadd.symm.trans (by rw [Int.modEq_zero_iff_dvd]; exact h1)
  exact (Int.modEq_zero_iff_dvd).mp hzero

#print axioms L6.L6_step_S15

/-- **S16** (author p. 4 §6.2): bổ đề 5 b) and bổ đề 4 at (4).

`(u+v) ⋮ n` is S15; bổ đề 5 b) then gives `(u+v, A) = n` and `A ⋮̸ n²`, and
bổ đề 4 with `m = n`, `a = u+v`, `b = A`, `c = t` gives `u+v = n^{ns−1}c^n`,
`A = n·c'^n`, `t = n^s(c·c')` — the print's (4'') (the print's exponent letter
order `sn − 1` equals `n s − 1`; see the chunk's F1 note 1).

Bổ đề 4's three `|·| ≥ 2` side conditions are met: `n ∣ u+v`, `n ∣ A`,
`n ∣ t` with `t≠0`, `A≠0` (its product is `t^n ≠ 0`), `u+v≠0`, and `n ≥ 3`
give `2 ≤ n ≤ |·|`. -/
theorem L6_step_S16 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t : ℤ}
    (ht : t ≠ 0) (htdvd : (n : ℤ) ∣ t) (h4 : (u + v) * L5.A ℤ n u v = t ^ n)
    (huv : Int.gcd u v = 1) (hw : (n : ℤ) ∣ u + v) :
    ∃ s : ℕ, ∃ c c' : ℤ, 1 ≤ s ∧ 2 ≤ n * s ∧ c ≠ 0 ∧ c' ≠ 0 ∧
      Int.gcd c c' = 1 ∧ ¬ (n : ℤ) ∣ c ∧ ¬ (n : ℤ) ∣ c' ∧
      t = (n : ℤ) ^ s * (c * c') ∧ u + v = (n : ℤ) ^ (n * s - 1) * c ^ n ∧
      L5.A ℤ n u v = (n : ℤ) * c' ^ n := by
  obtain ⟨hAdvd, hAnsq, hgcdA⟩ := (L5.L5_bo_de_5 hn hodd huv).2.1 hw
  have htne : t ^ n ≠ 0 := pow_ne_zero n ht
  have hw0 : u + v ≠ 0 := fun h => htne (by rw [← h4, h, zero_mul])
  have hA0 : L5.A ℤ n u v ≠ 0 := fun h => htne (by rw [← h4, h, mul_zero])
  have ha2 : 2 ≤ (u + v).natAbs :=
    le_trans hn.two_le (Nat.le_of_dvd (Int.natAbs_pos.mpr hw0) (Int.natCast_dvd.mp hw))
  have hb2 : 2 ≤ (L5.A ℤ n u v).natAbs :=
    le_trans hn.two_le (Nat.le_of_dvd (Int.natAbs_pos.mpr hA0) (Int.natCast_dvd.mp hAdvd))
  have hc2 : 2 ≤ t.natAbs :=
    le_trans hn.two_le (Nat.le_of_dvd (Int.natAbs_pos.mpr ht) (Int.natCast_dvd.mp htdvd))
  obtain ⟨s, c', c, hs1, hns, hc'0, hc0, hgcd', hnc', hnc, ht_eq, huv_eq, hA_eq⟩ :=
    L4.L4_bo_de_4 hn hodd hn.pos ha2 hb2 hc2 hw0 hA0 ht h4 hgcdA hAnsq
  refine ⟨s, c, c', hs1, hns, hc0, hc'0, ?_, hnc, hnc', ?_, huv_eq, hA_eq⟩
  · rwa [Int.gcd_comm] at hgcd'
  · rwa [mul_comm c' c] at ht_eq

#print axioms L6.L6_step_S16

/-- **S17** (author p. 4 §6.2, (5'')): `t^n − u − v = n^{ns−1}c^n(n·c'^n − 1)`
and `⋮ n²`.

`t^n = (n^s(c·c'))^n = n^{sn}c^n c'^n` and `u+v = n^{ns−1}c^n` factor the
difference as `n^{ns−1}c^n(n c'^n − 1)` (using `sn = ns`); `n² ∣ n^{ns−1}`
because `ns − 1 ≥ 2` (`n ≥ 3`, `s ≥ 1`). -/
theorem L6_step_S17 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t c c' : ℤ} {s : ℕ}
    (hs1 : 1 ≤ s) (ht : t = (n : ℤ) ^ s * (c * c'))
    (huv : u + v = (n : ℤ) ^ (n * s - 1) * c ^ n) :
    t ^ n - u - v = (n : ℤ) ^ (n * s - 1) * c ^ n * ((n : ℤ) * c' ^ n - 1) ∧
      (n : ℤ) ^ 2 ∣ t ^ n - u - v := by
  have hn3 : 3 ≤ n := by have h2 := hn.two_le; obtain ⟨j, hj⟩ := hodd; omega
  have hns3 : 3 ≤ n * s := by nlinarith [hn3, hs1]
  have hpos : 0 < n * s := by omega
  have hexp : n * s - 1 = 2 + (n * s - 1 - 2) := by omega
  have hexp2 : (n : ℤ) ^ (s * n) = (n : ℤ) ^ (n * s - 1) * (n : ℤ) := by
    rw [Nat.mul_comm s n]
    conv_lhs => rw [← Nat.sub_one_add_one_eq_of_pos hpos]
    rw [pow_succ]
  have hkey : t ^ n - u - v
      = (n : ℤ) ^ (n * s - 1) * c ^ n * ((n : ℤ) * c' ^ n - 1) := by
    have h1 : t ^ n - u - v = t ^ n - (u + v) := by ring
    rw [h1, ht, huv, mul_pow, ← pow_mul, hexp2]
    ring
  refine ⟨hkey, ?_⟩
  rw [hkey]
  have hpow : (n : ℤ) ^ (n * s - 1) = (n : ℤ) ^ 2 * (n : ℤ) ^ (n * s - 1 - 2) := by
    rw [← pow_add]
    conv_rhs => rw [show 2 + (n * s - 1 - 2) = n * s - 1 by omega]
  exact ⟨(n : ℤ) ^ (n * s - 1 - 2) * (c ^ n * ((n : ℤ) * c' ^ n - 1)), by rw [hpow]; ring⟩

#print axioms L6.L6_step_S17

/-- **S18** (author p. 4 §6.2): `(t−v) ⋮̸ n`, `(t−u) ⋮̸ n`, and bổ đề 5 a) at
the pairs `(t,−v)` and `(t,−u)`.

The print cites (5), (6); directly: `t ⋮ n` (the case hypothesis) together
with `(t−v) ⋮ n` would give `v ⋮ n`, against `uv ⋮̸ n` — and likewise `t−u`
gives `u ⋮ n`. Then bổ đề 5 a) — whose hypothesis is exactly `t−v ⋮̸ n` for
the pair `(t,−v)` — yields the two `gcd = 1` results and the two `Σ ⋮̸ n`
(the print's identical list). -/
theorem L6_step_S18 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t : ℤ}
    (huvn : ¬ (n : ℤ) ∣ u * v) (htdvd : (n : ℤ) ∣ t)
    (hut : Int.gcd u t = 1) (hvt : Int.gcd v t = 1) :
    ¬ (n : ℤ) ∣ t - v ∧ ¬ (n : ℤ) ∣ t - u ∧
      Int.gcd (t - v) (L5.A ℤ n t (-v)) = 1 ∧ ¬ (n : ℤ) ∣ L5.A ℤ n t (-v) ∧
      Int.gcd (t - u) (L5.A ℤ n t (-u)) = 1 ∧ ¬ (n : ℤ) ∣ L5.A ℤ n t (-u) := by
  have hnv : ¬ (n : ℤ) ∣ v := fun h => huvn (dvd_mul_of_dvd_right h u)
  have hnu : ¬ (n : ℤ) ∣ u := fun h => huvn (dvd_mul_of_dvd_left h v)
  have hntv : ¬ (n : ℤ) ∣ t - v := by
    intro h
    have h1 : (n : ℤ) ∣ t - (t - v) := dvd_sub htdvd h
    exact hnv (by convert h1 using 1; ring)
  have hntu : ¬ (n : ℤ) ∣ t - u := by
    intro h
    have h1 : (n : ℤ) ∣ t - (t - u) := dvd_sub htdvd h
    exact hnu (by convert h1 using 1; ring)
  have hcop_tv : Int.gcd t (-v) = 1 := by
    rw [L6_gcd_neg_right, Int.gcd_comm]
    exact hvt
  have hcop_tu : Int.gcd t (-u) = 1 := by
    rw [L6_gcd_neg_right, Int.gcd_comm]
    exact hut
  obtain ⟨h2a, h2b⟩ := (L5.L5_bo_de_5 hn hodd hcop_tv).1 (by simpa [sub_eq_add_neg] using hntv)
  obtain ⟨h3a, h3b⟩ := (L5.L5_bo_de_5 hn hodd hcop_tu).1 (by simpa [sub_eq_add_neg] using hntu)
  exact ⟨hntv, hntu, by simpa [sub_eq_add_neg] using h2a, h2b,
    by simpa [sub_eq_add_neg] using h3a, h3b⟩

#print axioms L6.L6_step_S18

/-- **S19** (author p. 4 §6.2): bổ đề 3 at (5) and (6) — the print's (5'), (6')
(labels re-used from 6.1) — together with the coprimality
`(a,b) = (a,c) = (c,b) = 1`.

Each pair `(t−v, Σ t^{n−1−i}v^i)`, `(t−u, Σ t^{n−1−i}u^i)` is a product of two
nonzero coprime integers equal to `u^n`, `v^n`; the `gcd = 1` inputs are S18's,
the nonvanishing follows from `u^n ≠ 0`, `v^n ≠ 0`. The two `⋮̸ n` facts for
the new `a', b'` come from S18's `Σ ⋮̸ n`. The three coprimalities are the
print's "(a,b) = (a,c) = (c,b) = 1": `a ∣ v`, `b ∣ u`, `c ∣ t` (as `c ∣ c·c'`
times `n^s`), so any common divisor of two of them divides the corresponding
coprime pair among `(u,v) = (v,t) = (u,t) = 1`. -/
theorem L6_step_S19 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t c c' : ℤ} {s : ℕ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h5 : (t - v) * L5.A ℤ n t (-v) = u ^ n) (h6 : (t - u) * L5.A ℤ n t (-u) = v ^ n)
    (hc5 : Int.gcd (t - v) (L5.A ℤ n t (-v)) = 1)
    (hc6 : Int.gcd (t - u) (L5.A ℤ n t (-u)) = 1)
    (hntv : ¬ (n : ℤ) ∣ t - v) (hntu : ¬ (n : ℤ) ∣ t - u)
    (hA5 : ¬ (n : ℤ) ∣ L5.A ℤ n t (-v)) (hA6 : ¬ (n : ℤ) ∣ L5.A ℤ n t (-u))
    (ht : t = (n : ℤ) ^ s * (c * c'))
    (huv : Int.gcd u v = 1) (hut : Int.gcd u t = 1) (hvt : Int.gcd v t = 1) :
    ∃ a a' b b' : ℤ,
      a ≠ 0 ∧ a' ≠ 0 ∧ Int.gcd a a' = 1 ∧ v = a * a' ∧ t - u = a ^ n ∧
        L5.A ℤ n t (-u) = a' ^ n ∧ ¬ (n : ℤ) ∣ a ∧ ¬ (n : ℤ) ∣ a' ∧
      b ≠ 0 ∧ b' ≠ 0 ∧ Int.gcd b b' = 1 ∧ u = b * b' ∧ t - v = b ^ n ∧
        L5.A ℤ n t (-v) = b' ^ n ∧ ¬ (n : ℤ) ∣ b ∧ ¬ (n : ℤ) ∣ b' ∧
      Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd c b = 1 := by
  have hune : u ^ n ≠ 0 := pow_ne_zero n hu
  have hvne : v ^ n ≠ 0 := pow_ne_zero n hv
  have htvne : t - v ≠ 0 := fun h => hune (by rw [← h5, h, zero_mul])
  have hA5ne : L5.A ℤ n t (-v) ≠ 0 := fun h => hune (by rw [← h5, h, mul_zero])
  have htune : t - u ≠ 0 := fun h => hvne (by rw [← h6, h, zero_mul])
  have hA6ne : L5.A ℤ n t (-u) ≠ 0 := fun h => hvne (by rw [← h6, h, mul_zero])
  obtain ⟨b, b', hb0, hb'0, hgcd_bb', hu_bb', htv_b, hA_b'⟩ :=
    L3.L3_bo_de_3 hodd hn.pos htvne hA5ne hu h5 hc5
  obtain ⟨a, a', ha0, ha'0, hgcd_aa', hv_aa', htu_a, hA_a'⟩ :=
    L3.L3_bo_de_3 hodd hn.pos htune hA6ne hv h6 hc6
  have hnb : ¬ (n : ℤ) ∣ b := fun h => hntv (by rw [htv_b]; exact dvd_pow h hn.ne_zero)
  have hnb' : ¬ (n : ℤ) ∣ b' := fun h => hA5 (by rw [hA_b']; exact dvd_pow h hn.ne_zero)
  have hna : ¬ (n : ℤ) ∣ a := fun h => hntu (by rw [htu_a]; exact dvd_pow h hn.ne_zero)
  have hna' : ¬ (n : ℤ) ∣ a' := fun h => hA6 (by rw [hA_a']; exact dvd_pow h hn.ne_zero)
  have ha_v : a ∣ v := by rw [hv_aa']; exact dvd_mul_right a a'
  have hb_u : b ∣ u := by rw [hu_bb']; exact dvd_mul_right b b'
  have hc_t : c ∣ t := by rw [ht]; exact dvd_mul_of_dvd_right (dvd_mul_right c c') _
  have hvu : Int.gcd v u = 1 := by rw [Int.gcd_comm]; exact huv
  have htu : Int.gcd t u = 1 := by rw [Int.gcd_comm]; exact hut
  exact ⟨a, a', b, b', ha0, ha'0, hgcd_aa', hv_aa', htu_a, hA_a', hna, hna',
    hb0, hb'0, hgcd_bb', hu_bb', htv_b, hA_b', hnb, hnb',
    L6_gcd_eq_one_of_dvd ha_v hb_u hvu,
    L6_gcd_eq_one_of_dvd ha_v hc_t hvt,
    L6_gcd_eq_one_of_dvd hc_t hb_u htu⟩

#print axioms L6.L6_step_S19

/-- **S20 + S21 + S22** (author p. 4 §6.2): "Lập luận như 6.1" gives
`b' = 1 + n k₂`, `a' = 1 + n k₁`; then (5''), (6''), the three-term identity
`(u^n − t + v) + (v^n − t + u) − (t^n − u − v) = 2(u+v−t)` and
`(u+v−t) ⋮ n²`.

This is literally the author's "same argument as 6.1": `L6_step_S10` at
`(t,−v)`, `(t,−u)` and `L6_step_S12` (which already carries the three-term
identity and the halving), the only new input being S17's
`(t^n − u − v) ⋮ n²`. -/
theorem L6_step_S20_S22 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t a a' b b' : ℤ}
    (hsol : u ^ n + v ^ n = t ^ n)
    (hntv : ¬ (n : ℤ) ∣ t - v) (hntu : ¬ (n : ℤ) ∣ t - u)
    (hA5 : L5.A ℤ n t (-v) = b' ^ n) (hA6 : L5.A ℤ n t (-u) = a' ^ n)
    (hnb' : ¬ (n : ℤ) ∣ b') (hna' : ¬ (n : ℤ) ∣ a')
    (hu : u = b * b') (htv : t - v = b ^ n) (hv : v = a * a') (htu : t - u = a ^ n)
    (h17 : (n : ℤ) ^ 2 ∣ t ^ n - u - v) :
    (∃ k : ℤ, b' = 1 + (n : ℤ) * k) ∧ (∃ k : ℤ, a' = 1 + (n : ℤ) * k) ∧
      (n : ℤ) ^ 2 ∣ u ^ n - t + v ∧ (n : ℤ) ^ 2 ∣ v ^ n - t + u ∧
      (u ^ n - t + v) + (v ^ n - t + u) - (t ^ n - u - v) = 2 * (u + v - t) ∧
      (n : ℤ) ^ 2 ∣ u + v - t := by
  obtain ⟨⟨k₂, hk₂⟩, ⟨k₁, hk₁⟩⟩ := L6_step_S10 hn hodd hntv hntu hA5 hA6 hnb' hna'
  obtain ⟨h1, h2, hid, h3⟩ := L6_step_S12 hodd hsol hu htv hk₂ hv htu hk₁ h17
  exact ⟨⟨k₂, hk₂⟩, ⟨k₁, hk₁⟩, h1, h2, hid, h3⟩

#print axioms L6.L6_step_S20_S22

/-- `(N·x^{n−1} − x', x) = 1` from `(x,x') = 1` (`n ≥ 2`) — the version of
`L6_gcd_pow_sub_eq_one` with an extra factor `N`; 6.2 needs it with
`N = n^{ns−1−s}` at `x = c`. -/
lemma L6_gcd_mul_pow_sub_eq_one {n : ℕ} (hn2 : 2 ≤ n) {x x' N : ℤ}
    (h : Int.gcd x x' = 1) : Int.gcd (N * x ^ (n - 1) - x') x = 1 := by
  have hsplit : x ^ (n - 1) = x * x ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']
  have hshift : Int.gcd (N * x ^ (n - 1) - x') x = Int.gcd (-x') x := by
    have hh := Int.gcd_add_mul_right_left x (-x') (N * x ^ (n - 2))
    rw [show -x' + (N * x ^ (n - 2)) * x = N * x ^ (n - 1) - x' by rw [hsplit]; ring] at hh
    exact hh
  rw [hshift, L6_gcd_neg_left, Int.gcd_comm]
  exact h

#print axioms L6.L6_gcd_mul_pow_sub_eq_one

/-- **S23** (author p. 4 §6.2): `u+v−t = n^s c(n^{ns−1−s}c^{n−1} − c')
= a(a'−a^{n−1}) = b(b'−b^{n−1}) = n^s a b c k` with `s ≥ 2`, `k ≠ 0`,
`(k,a) = (k,b) = (k,c) = 1`, `k ⋮̸ n`.

Unlike 6.1 the `n`-power `s` is *given* — it is (4'')'s — and it is maximal:
bổ đề 4 gives `n ∤ c`, `n ∤ c'`, S16 gives they are the two factors of
`t = n^s·(c·c')`, and the bracket `n^{ns−1−s}c^{n−1} − c' ≡ −c' (mod n)` is
`⋮̸ n` because `ns−1−s ≥ 1`. So `u+v−t = n^s·Y` with `n ∤ Y`, and S22's
`n² ∣ u+v−t` forces `s ≥ 2`. `a b c ∣ Y` (`a`, `b` from (5')/(6'), `c` from
the displayed factorisation; `gcd(abc,n) = 1`), so `Y = a b c k`; then
`k ≠ 0` (the print's §6.2.1 excludes `X = 0`, cf. `L6_zero_case`), `n ∤ k`,
and the three gcds from `k ∣ X/a`, `k ∣ X/b` and `k ∣ Y/c = n^{ns−1−s}c^{n−1} − c'`
with `(a,a') = (b,b') = (c,c') = 1`. -/
theorem L6_step_S23 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n)
    {u v t a a' b b' c c' : ℤ} {s : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hna : ¬ (n : ℤ) ∣ a) (hnb : ¬ (n : ℤ) ∣ b) (hnc : ¬ (n : ℤ) ∣ c)
    (hnc' : ¬ (n : ℤ) ∣ c')
    (hab : Int.gcd a b = 1) (hac : Int.gcd a c = 1) (hcb : Int.gcd c b = 1)
    (haa' : Int.gcd a a' = 1) (hbb' : Int.gcd b b' = 1) (hcc' : Int.gcd c c' = 1)
    (hs1 : 1 ≤ s) (ht : t = (n : ℤ) ^ s * (c * c'))
    (huv : u + v = (n : ℤ) ^ (n * s - 1) * c ^ n)
    (hva : v = a * a') (htu : t - u = a ^ n) (hu : u = b * b') (htv : t - v = b ^ n)
    (hX0 : u + v - t ≠ 0) (h2 : (n : ℤ) ^ 2 ∣ u + v - t) :
    ∃ k : ℤ, 2 ≤ s ∧ u + v - t = (n : ℤ) ^ s * (a * b * c * k) ∧ k ≠ 0 ∧
      ¬ (n : ℤ) ∣ k ∧ Int.gcd k a = 1 ∧ Int.gcd k b = 1 ∧ Int.gcd k c = 1 := by
  have hn3 : 3 ≤ n := by have h2 := hn.two_le; obtain ⟨j, hj⟩ := hodd; omega
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have hbnd : s + 2 ≤ n * s := by nlinarith [hn3, hs1]
  have han : a ^ n = a * a ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
  have hbn : b ^ n = b * b ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
  have hcn : c ^ n = c * c ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
  have hexp : n * s - 1 = s + (n * s - 1 - s) := by omega
  have h1 : (n : ℤ) ^ (n * s - 1) = (n : ℤ) ^ s * (n : ℤ) ^ (n * s - 1 - s) := by
    conv_rhs => rw [← pow_add]
    conv_lhs => rw [hexp]
  have hXaeq : u + v - t = a * (a' - a ^ (n - 1)) := by
    have h : u + v - t = v - (t - u) := by ring
    rw [h, hva, htu, han]
    ring
  have hXbeq : u + v - t = b * (b' - b ^ (n - 1)) := by
    have h : u + v - t = u - (t - v) := by ring
    rw [h, hu, htv, hbn]
    ring
  have hXs : u + v - t
      = (n : ℤ) ^ s * (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) := by
    rw [ht, huv, h1, hcn]
    ring
  have hbr : ¬ (n : ℤ) ∣ ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c') := by
    intro hd
    have h1' : (n : ℤ) ∣ (n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) := by
      have hne : n * s - 1 - s ≠ 0 := by omega
      exact dvd_mul_of_dvd_left (dvd_pow_self (n : ℤ) hne) _
    have h2' : (n : ℤ) ∣ c' := by
      have h := dvd_sub h1' hd
      have hring : (n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1)
          - ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c') = c' := by ring
      rwa [hring] at h
    exact hnc' h2'
  have hYndvd : ¬ (n : ℤ) ∣ (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) :=
    fun hd => hbr ((Int.Prime.dvd_mul' hn hd).resolve_left hnc)
  have hY0 : (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) ≠ 0 :=
    fun h => hX0 (by rw [hXs, h, mul_zero])
  have hs2 : 2 ≤ s := by
    by_contra hcon
    have hnsplit : (n : ℤ) ^ 2 = (n : ℤ) ^ s * ((n : ℤ) * (n : ℤ) ^ (1 - s)) := by
      rw [← mul_assoc, ← pow_succ, ← pow_add]
      congr 1
      omega
    have hd : (n : ℤ) ^ s * ((n : ℤ) * (n : ℤ) ^ (1 - s)) ∣
        (n : ℤ) ^ s * (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) := by
      rw [← hnsplit, ← hXs]
      exact h2
    have hd2 : (n : ℤ) * (n : ℤ) ^ (1 - s) ∣
        (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) :=
      (Int.mul_dvd_mul_iff_left (pow_ne_zero s hnz)).mp hd
    exact hYndvd (dvd_trans (dvd_mul_right _ _) hd2)
  have hna_cop : IsCoprime (n : ℤ) a :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_comm]; exact L5.L5_gcd_eq_one_of_not_dvd hn hna)
  have hnb_cop : IsCoprime (n : ℤ) b :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_comm]; exact L5.L5_gcd_eq_one_of_not_dvd hn hnb)
  have hnc_cop : IsCoprime (n : ℤ) c :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_comm]; exact L5.L5_gcd_eq_one_of_not_dvd hn hnc)
  have hcop_a : IsCoprime a ((n : ℤ) ^ s) := hna_cop.symm.pow_right
  have hcop_b : IsCoprime b ((n : ℤ) ^ s) := hnb_cop.symm.pow_right
  have haX : a ∣ u + v - t := by rw [hXaeq]; exact dvd_mul_right a _
  have hbX : b ∣ u + v - t := by rw [hXbeq]; exact dvd_mul_right b _
  have hcX : c ∣ u + v - t := by
    rw [hXs]
    exact dvd_mul_of_dvd_right (dvd_mul_right c _) _
  have haY : a ∣ (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) := by
    have h : a ∣ (n : ℤ) ^ s * (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) := by
      rw [← hXs]
      exact haX
    exact hcop_a.dvd_of_dvd_mul_left h
  have hbY : b ∣ (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) := by
    have h : b ∣ (n : ℤ) ^ s * (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) := by
      rw [← hXs]
      exact hbX
    exact hcop_b.dvd_of_dvd_mul_left h
  have hcY : c ∣ (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) :=
    dvd_mul_right c _
  have habY : a * b ∣ (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr hab).mul_dvd haY hbY
  have habc_cop : IsCoprime (a * b) c :=
    IsCoprime.mul_left (Int.isCoprime_iff_gcd_eq_one.mpr hac)
      (Int.isCoprime_iff_gcd_eq_one.mpr hcb).symm
  have habcY : a * b * c ∣ (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c')) :=
    habc_cop.mul_dvd habY hcY
  obtain ⟨k, hk⟩ := habcY
  have hXk : u + v - t = (n : ℤ) ^ s * ((a * b * c) * k) := by rw [hXs, hk]
  have hk0 : k ≠ 0 := fun h => hY0 (by rw [hk, h, mul_zero])
  have hnk : ¬ (n : ℤ) ∣ k := fun h =>
    hYndvd (by rw [hk]; exact dvd_mul_of_dvd_right h (a * b * c))
  have hAa : a' - a ^ (n - 1) = (n : ℤ) ^ s * (b * (c * k)) := by
    have h : a * (a' - a ^ (n - 1)) = a * ((n : ℤ) ^ s * (b * (c * k))) := by
      rw [← hXaeq, hXs, hk]
      ring
    exact mul_left_cancel₀ ha h
  have hA' : k ∣ a' - a ^ (n - 1) := by
    rw [hAa]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_left k c) b) ((n : ℤ) ^ s)
  have hBa : b' - b ^ (n - 1) = (n : ℤ) ^ s * (a * (c * k)) := by
    have h : b * (b' - b ^ (n - 1)) = b * ((n : ℤ) ^ s * (a * (c * k))) := by
      rw [← hXbeq, hXs, hk]
      ring
    exact mul_left_cancel₀ hb h
  have hB' : k ∣ b' - b ^ (n - 1) := by
    rw [hBa]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_left k c) a) ((n : ℤ) ^ s)
  have hY' : (n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c' = a * b * k := by
    have hCY : c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c') = (a * b * c) * k := by
      have h : (n : ℤ) ^ s * (c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c'))
          = (n : ℤ) ^ s * ((a * b * c) * k) := by rw [← hXs, hXk]
      exact mul_left_cancel₀ (pow_ne_zero s hnz) h
    have h2' : c * ((n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c') = c * (a * b * k) := by
      rw [hCY]
      ring
    exact mul_left_cancel₀ hc h2'
  have hC' : k ∣ (n : ℤ) ^ (n * s - 1 - s) * c ^ (n - 1) - c' := by
    rw [hY']
    exact dvd_mul_left k (a * b)
  exact ⟨k, hs2, hXk, hk0, hnk,
    L6_gcd_eq_one_of_dvd_left hA' (L6_gcd_sub_pow_eq_one hn.two_le haa'),
    L6_gcd_eq_one_of_dvd_left hB' (L6_gcd_sub_pow_eq_one hn.two_le hbb'),
    L6_gcd_eq_one_of_dvd_left hC' (L6_gcd_mul_pow_sub_eq_one hn.two_le hcc')⟩

#print axioms L6.L6_step_S23

/-- **S24** (author p. 4 §6.2 end, the displayed conclusion): case 6.2's
conclusion, `v = a^n + X`, `u = b^n + X`, `t = n^{ns−1}c^n − X`,
`a^n + b^n = n^{ns−1}c^n − 2X` with `X = n^s a b c k` and `h = n^{ns−1}c^n`
((4'')).

Same computation as S14, with `h` now `(4'')`'s `n^{ns−1}c^n` instead of
`c^n`: the first two come from `X = b(b'−b^{n−1})`, `X = a(a'−a^{n−1})` and
`u = b·b'`, `v = a·a'`; the third is `t = n^s(c·c') = h − X`; the last from
`a^n = v − X`, `b^n = u − X`. The author's S0 nonvanishing `a ≠ 0`, `b ≠ 0`
are carried unused (`_ha`, `_hb`). -/
theorem L6_step_S24 {n : ℕ} (hodd : Odd n) {u v t a a' b b' c c' k : ℤ} {s : ℕ}
    (_ha : a ≠ 0) (_hb : b ≠ 0)
    (huv : u + v = (n : ℤ) ^ (n * s - 1) * c ^ n) (ht : t = (n : ℤ) ^ s * (c * c'))
    (hu' : u = b * b') (hv' : v = a * a')
    (hXa : u + v - t = a * (a' - a ^ (n - 1)))
    (hXb : u + v - t = b * (b' - b ^ (n - 1)))
    (hXk : u + v - t = (n : ℤ) ^ s * (a * b * c * k)) :
    v = a ^ n + (n : ℤ) ^ s * (a * b * c * k) ∧
      u = b ^ n + (n : ℤ) ^ s * (a * b * c * k) ∧
      t = (n : ℤ) ^ (n * s - 1) * c ^ n - (n : ℤ) ^ s * (a * b * c * k) ∧
      a ^ n + b ^ n
        = (n : ℤ) ^ (n * s - 1) * c ^ n - 2 * ((n : ℤ) ^ s * (a * b * c * k)) := by
  have hn0 : 0 < n := by obtain ⟨j, hj⟩ := hodd; omega
  have han : a ^ n = a * a ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn0]
  have hbn : b ^ n = b * b ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn0]
  have hub : u = b ^ n + (n : ℤ) ^ s * (a * b * c * k) := by
    have h1 : b * b' = b ^ n + (u + v - t) := by rw [hXb, hbn]; ring
    rw [hu', h1, hXk]
  have hav : v = a ^ n + (n : ℤ) ^ s * (a * b * c * k) := by
    have h1 : a * a' = a ^ n + (u + v - t) := by rw [hXa, han]; ring
    rw [hv', h1, hXk]
  have hat : t = (n : ℤ) ^ (n * s - 1) * c ^ n - (n : ℤ) ^ s * (a * b * c * k) := by
    have h1 : t = (n : ℤ) ^ (n * s - 1) * c ^ n - (u + v - t) := by rw [ht, huv]; ring
    rw [h1, hXk]
  refine ⟨hav, hub, hat, ?_⟩
  have hA : a ^ n = v - (n : ℤ) ^ s * (a * b * c * k) := by omega
  have hB : b ^ n = u - (n : ℤ) ^ s * (a * b * c * k) := by omega
  have hC : (n : ℤ) ^ (n * s - 1) * c ^ n = u + v := huv.symm
  omega

#print axioms L6.L6_step_S24

/-- **S25 + S26** (author p. 4 §6.2.1): the case `k = 0` is absurd.

The print: "Khi `k = 0` thì `t−u = v`, `t−v = u`, hay `a^n = a·a'`,
`b^n = b·b'`; tức là `a^{n−1} = a'`, `b^{n−1} = b'`. Suy ra
`|a| = |a'| = |b| = |b'| = 1`" — followed by the `t ∈ {−2,0,2}`, `t^n = 2`
check that the print calls "vô lý". That argument is `L6_zero_case` (the same
one used to exclude `k = 0` in 6.1); `k = 0` gives `u+v−t = n^s a b c k = 0`. -/
theorem L6_step_S25_S26 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n)
    {u v t a a' b b' c k : ℤ} {s : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) (hsol : u ^ n + v ^ n = t ^ n)
    (hv : v = a * a') (htu : t - u = a ^ n) (hg_aa' : Int.gcd a a' = 1)
    (hu : u = b * b') (htv : t - v = b ^ n) (hg_bb' : Int.gcd b b' = 1)
    (hk : k = 0) (hXk : u + v - t = (n : ℤ) ^ s * (a * b * c * k)) : False :=
  L6_zero_case hn hodd ha hb ht hsol hv htu hg_aa' hu htv hg_bb'
    (by rw [hXk, hk]; simp)

#print axioms L6.L6_step_S25_S26

/-- **Assembly** (author p. 3–4, bổ đề 6): the two cases 6.1 / 6.2, and inside
6.2 the sub-case `k = 0` (§6.2.1).

`h` is the print's `h`: `c^n = u+v` in 6.1, `n^{ns−1}c^n = u+v` in 6.2. The
split on `t ⋮ n` is the print's; both branches emit the same integers
`a, b, c, k` and exponent `s`, and the two conditional clauses on `h` are the
print's "với `h = c^n` khi `t ⋮̸ n` hoặc `h = n^{ns−1}c^n` khi `t ⋮ n`". The
`k = 0` sub-case is absorbed by `L6_zero_case` in each branch (see `S13`/
`S25+S26` above). -/
theorem L6_bo_de_6 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v t : ℤ}
    (hu : u ≠ 0) (hv : v ≠ 0) (ht : t ≠ 0)
    (hsol : u ^ n + v ^ n = t ^ n)
    (huv : Int.gcd u v = 1) (hut : Int.gcd u t = 1) (hvt : Int.gcd v t = 1)
    (huvn : ¬ (n : ℤ) ∣ u * v) :
    ∃ a b c k h : ℤ, ∃ s : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ k ≠ 0 ∧
      Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd c b = 1 ∧
      Int.gcd a k = 1 ∧ Int.gcd b k = 1 ∧ Int.gcd c k = 1 ∧
      ¬ (n : ℤ) ∣ a ∧ ¬ (n : ℤ) ∣ b ∧ ¬ (n : ℤ) ∣ c ∧ ¬ (n : ℤ) ∣ k ∧
      2 ≤ s ∧
      v = a ^ n + (n : ℤ) ^ s * (a * b * c * k) ∧
      u = b ^ n + (n : ℤ) ^ s * (a * b * c * k) ∧
      t = h - (n : ℤ) ^ s * (a * b * c * k) ∧
      a ^ n + b ^ n = h - 2 * ((n : ℤ) ^ s * (a * b * c * k)) ∧
      (¬ (n : ℤ) ∣ t → h = c ^ n) ∧ ((n : ℤ) ∣ t → h = (n : ℤ) ^ (n * s - 1) * c ^ n) := by
  obtain ⟨h4, h5, h6⟩ := L6_step_S2 hodd hsol
  by_cases ht6 : (n : ℤ) ∣ t
  · -- case 6.2: t ⋮ n
    obtain ⟨e, c, c', hs1, hns, hc0, hc'0, hgcd_cc', hnc, hnc', ht_eq, huv_eq, hA_eq⟩ :=
      L6_step_S16 hn hodd ht ht6 h4 huv (L6_step_S15 hn hsol huvn ht6)
    obtain ⟨hntv, hntu, hc5, hA5, hc6, hA6⟩ := L6_step_S18 hn hodd huvn ht6 hut hvt
    obtain ⟨a, a', b, b', ha0, ha'0, hgcd_aa', hv_aa', htu_a, hA_a', hna, hna',
      hb0, hb'0, hgcd_bb', hu_bb', htv_b, hA_b', hnb, hnb', hgab, hgac, hgcb⟩ :=
      L6_step_S19 hn hodd hu hv h5 h6 hc5 hc6 hntv hntu hA5 hA6 ht_eq huv hut hvt
    obtain ⟨_, h17dvd⟩ := L6_step_S17 hn hodd hs1 ht_eq huv_eq
    obtain ⟨⟨k₂, hk₂⟩, ⟨k₁, hk₁⟩, -, -, -, h22⟩ :=
      L6_step_S20_S22 hn hodd hsol hntv hntu hA_b' hA_a' hnb' hna'
        hu_bb' htv_b hv_aa' htu_a h17dvd
    have han : a ^ n = a * a ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
    have hbn : b ^ n = b * b ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
    have hXa : u + v - t = a * (a' - a ^ (n - 1)) := by
      have h : u + v - t = v - (t - u) := by ring
      rw [h, hv_aa', htu_a, han]
      ring
    have hXb : u + v - t = b * (b' - b ^ (n - 1)) := by
      have h : u + v - t = u - (t - v) := by ring
      rw [h, hu_bb', htv_b, hbn]
      ring
    have hX0 : u + v - t ≠ 0 := by
      intro h
      exact L6_zero_case hn hodd ha0 hb0 ht hsol hv_aa' htu_a hgcd_aa'
        hu_bb' htv_b hgcd_bb' h
    obtain ⟨k, hs2, hXk, hk0, hnk, hgka, hgkb, hgkc⟩ :=
      L6_step_S23 hn hodd ha0 hb0 hc0 hna hnb hnc hnc'
        hgab hgac hgcb hgcd_aa' hgcd_bb' hgcd_cc' hs1 ht_eq huv_eq
        hv_aa' htu_a hu_bb' htv_b hX0 h22
    obtain ⟨hav, hub, hat, hab⟩ :=
      L6_step_S24 hodd ha0 hb0 huv_eq ht_eq hu_bb' hv_aa' hXa hXb hXk
    have hgak : Int.gcd a k = 1 := by rw [Int.gcd_comm]; exact hgka
    have hgbk : Int.gcd b k = 1 := by rw [Int.gcd_comm]; exact hgkb
    have hgck : Int.gcd c k = 1 := by rw [Int.gcd_comm]; exact hgkc
    exact ⟨a, b, c, k, (n : ℤ) ^ (n * e - 1) * c ^ n, e, ha0, hb0, hc0, hk0,
      hgab, hgac, hgcb, hgak, hgbk, hgck, hna, hnb, hnc, hnk, hs2, hav, hub, hat, hab,
      (fun hdvd => absurd ht6 hdvd), (fun _ => rfl)⟩
  · -- case 6.1: t ⋮̸ n
    obtain ⟨hnuv, hntv, hntu⟩ := L6_step_S3 hn hodd hsol huvn ht6
    obtain ⟨⟨c, c', hc0, hc'0, hgcd_cc', ht_cc', huv_c, hA_c', hnc, hnc'⟩,
      ⟨b, b', hb0, hb'0, hgcd_bb', hu_bb', htv_b, hA_b', hnb, hnb'⟩,
      ⟨a, a', ha0, ha'0, hgcd_aa', hv_aa', htu_a, hA_a', hna, hna'⟩⟩ :=
      L6_step_S5 hn hodd hu hv ht hsol huv hut hvt huvn ht6
    obtain ⟨hgab, hgac, hgcb⟩ := L6_step_S6 hu_bb' hv_aa' ht_cc' huv hut hvt
    obtain ⟨k₃, hk₃⟩ := L6_step_S9 hn hodd hnuv hA_c' hnc'
    obtain ⟨⟨k₂, hk₂⟩, ⟨k₁, hk₁⟩⟩ := L6_step_S10 hn hodd hntv hntu hA_b' hA_a' hnb' hna'
    obtain ⟨-, h11⟩ := L6_step_S11 huv_c ht_cc' hk₃
    obtain ⟨-, -, -, hXt⟩ := L6_step_S12 hodd hsol hu_bb' htv_b hk₂ hv_aa' htu_a hk₁ h11
    have han : a ^ n = a * a ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
    have hbn : b ^ n = b * b ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
    have hcn : c ^ n = c * c ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hn.pos]
    have hXa : u + v - t = a * (a' - a ^ (n - 1)) := by
      have h : u + v - t = v - (t - u) := by ring
      rw [h, hv_aa', htu_a, han]
      ring
    have hXb : u + v - t = b * (b' - b ^ (n - 1)) := by
      have h : u + v - t = u - (t - v) := by ring
      rw [h, hu_bb', htv_b, hbn]
      ring
    have hXc : u + v - t = c * (c ^ (n - 1) - c') := by
      rw [huv_c, ht_cc', hcn]
      ring
    have hX0 : u + v - t ≠ 0 := by
      intro h
      exact L6_zero_case hn hodd ha0 hb0 ht hsol hv_aa' htu_a hgcd_aa'
        hu_bb' htv_b hgcd_bb' h
    obtain ⟨e, k, hs2, hXk, hk0, hnk, hgka, hgkb, hgkc⟩ :=
      L6_step_S13 hn ha0 hb0 hc0 hna hnb hnc hgab hgac hgcb
        hgcd_aa' hgcd_bb' hgcd_cc' hXa hXb hXc hX0 hXt
    obtain ⟨hav, hub, hat, hab⟩ :=
      L6_step_S14 hodd ha0 hb0 hc0 huv_c ht_cc' hu_bb' hv_aa' hXa hXb hXc hXk
    have hgak : Int.gcd a k = 1 := by rw [Int.gcd_comm]; exact hgka
    have hgbk : Int.gcd b k = 1 := by rw [Int.gcd_comm]; exact hgkb
    have hgck : Int.gcd c k = 1 := by rw [Int.gcd_comm]; exact hgkc
    exact ⟨a, b, c, k, c ^ n, e, ha0, hb0, hc0, hk0,
      hgab, hgac, hgcb, hgak, hgbk, hgck, hna, hnb, hnc, hnk, hs2, hav, hub, hat, hab,
      (fun _ => rfl), (fun hdvd => absurd hdvd ht6)⟩

#print axioms L6.L6_bo_de_6

end L6
