import Mathlib
import L5.Basic
import L7F2.Basic
import L7F3.Basic

/-!
# Lemma 7 (bổ đề 7) — display (18) and the mod-n² form (22') of GT3
(chunk L7-FRAG-04)

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 2 top, the (18) group and the (22') form;
  * proof: p. 5 §7, the two bullets after the non-divisibility "(đpcm)".

The literal transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L7-FRAG-04.yml`:

  S12    "Vì c^n + b^n ≢ 0 (mod n), b^{3n}+c^{3n} = (b^n+c^n)[(c^n−b^n)²+b^nc^n]
         ≡ (b^n+c^n)(a^{2n}+b^nc^n) ≡ 0 (mod n²) nên a^{2n}+b^nc^n ≡ 0 (mod n²)"
                                                              -> L7F4_step_S12
  S13    "Chứng minh tương tự ta cũng có
         b^{2n}+a^nc^n ≡ c^{2n}−a^nb^n ≡ 0 (mod n²)"          -> L7F4_step_S13
  S14    "Ta có c^{2n}−a^nb^n ≡ 0 (mod n²) ⇒ … ⇒
         b^{n(n−2)}+a^{n(n−2)}−c^{n(n−2)} ≡ 0 (mod n²) (đpcm)" -> L7F4_step_S14

## Encoding decisions

* `L7F4_sum_chain` is S12's argument with the pair abstracted: the printed
  instance is `(U, V) = (a, b)` (`L7F4_step_S12`, using the print's (19)) and
  the "tương tự" instance is `(U, V) = (b, a)` (`L7F4_step_S13`, using S10's
  `a^{3n}+c^{3n} ≡ 0`) — the print's own claim of analogy.
* The cancellations are legitimate mod `n²` because the cancelled factors are
  ≢ 0 mod `n` (so coprime to `n²`): `b^n+c^n` (S5b/S3_S4 of L7-FRAG-01),
  `a^n+c^n` (S5b), `a^n−b^n` (S5c) and `a^nb^nc^n` (S0) — these are exactly
  the non-divisibility facts chunk L7-FRAG-01 verified.
* S13's second conjunct uses the difference factorization
  `a^{3n}−b^{3n} = (a^n−b^n)(a^{2n}+a^nb^n+b^{2n})` (the "tương tự" of S12's
  sum factorization) together with `c^{2n} ≡ (a^n+b^n)²`.
* S14 is the printed chain: `c^{2n} ≡ c^n(a^n+b^n)` by (b), then 5d at
  `a, b, c` to raise the three terms, then the cancellation of `a^nb^nc^n`
  (the printed step has no comment for it — the author's own S0 hypothesis
  makes it invertible mod `n²`).
-/

namespace L7

/-- The printed S12 argument with the pair abstracted (the print's own
"chứng minh tương tự"): from

  * `V^{3n}+c^{3n} ≡ 0 (mod n²)` (the printed (19) at `(b, c)`, or S10's
    `a^{3n}+c^{3n} ≡ 0` at `(a, c)`),
  * `c^n ≡ U^n + V^n (mod n²)` (the printed (b)),
  * `V^n + c^n ⋮̸ n`,

the factorization `V^{3n}+c^{3n} = (V^n+c^n)((c^n−V^n)²+V^nc^n)`, the
replacement `(c^n−V^n)² ≡ U^{2n}` and the cancellation of `V^n+c^n`
(invertible mod `n²` because it is ≢ 0 mod `n`) give `U^{2n}+V^nc^n ≡ 0`. -/
theorem L7F4_sum_chain {n : ℕ} (hn : Nat.Prime n) {U V c : ℤ}
    (h3n : (V ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h1 : (c ^ n : ℤ) ≡ U ^ n + V ^ n [ZMOD (n ^ 2 : ℤ)])
    (hc : ¬ (n : ℤ) ∣ V ^ n + c ^ n) :
    (U ^ (2 * n) + V ^ n * c ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have hV3 : (V ^ (3 * n) : ℤ) = (V ^ n) ^ 3 := by rw [Nat.mul_comm 3 n, pow_mul]
  have hc3 : (c ^ (3 * n) : ℤ) = (c ^ n) ^ 3 := by rw [Nat.mul_comm 3 n, pow_mul]
  -- the printed factorization
  have hfac : (V ^ (3 * n) + c ^ (3 * n) : ℤ)
      = (V ^ n + c ^ n) * ((c ^ n - V ^ n) ^ 2 + V ^ n * c ^ n) := by
    rw [hV3, hc3]; ring
  have hdvd0 : (n ^ 2 : ℤ) ∣ (V ^ n + c ^ n) * ((c ^ n - V ^ n) ^ 2 + V ^ n * c ^ n) := by
    have h := Int.modEq_zero_iff_dvd.mp h3n
    rwa [hfac] at h
  -- "(c^n − V^n)² ≡ U^{2n}"
  have hsub : (c ^ n - V ^ n : ℤ) ≡ U ^ n [ZMOD (n ^ 2 : ℤ)] := by
    have h := Int.ModEq.sub h1 (Int.ModEq.refl (V ^ n))
    simpa using h
  have hsq : ((c ^ n - V ^ n) ^ 2 : ℤ) ≡ U ^ (2 * n) [ZMOD (n ^ 2 : ℤ)] := by
    have h := hsub.pow 2
    have hU2 : ((U ^ n) ^ 2 : ℤ) = U ^ (2 * n) := by rw [Nat.mul_comm 2 n, pow_mul]
    rwa [hU2] at h
  have hdvd1 : (n ^ 2 : ℤ)
      ∣ (U ^ (2 * n) + V ^ n * c ^ n) - ((c ^ n - V ^ n) ^ 2 + V ^ n * c ^ n) := by
    have h := Int.modEq_iff_dvd.mp hsq
    have hid : (U ^ (2 * n) + V ^ n * c ^ n) - ((c ^ n - V ^ n) ^ 2 + V ^ n * c ^ n)
        = U ^ (2 * n) - (c ^ n - V ^ n) ^ 2 := by ring
    rwa [hid]
  have htarget : (n ^ 2 : ℤ) ∣ (V ^ n + c ^ n) * (U ^ (2 * n) + V ^ n * c ^ n) := by
    have h := dvd_add hdvd0 (dvd_mul_of_dvd_right hdvd1 (V ^ n + c ^ n))
    have hid : (V ^ n + c ^ n) * ((c ^ n - V ^ n) ^ 2 + V ^ n * c ^ n)
        + (V ^ n + c ^ n) * ((U ^ (2 * n) + V ^ n * c ^ n)
            - ((c ^ n - V ^ n) ^ 2 + V ^ n * c ^ n))
        = (V ^ n + c ^ n) * (U ^ (2 * n) + V ^ n * c ^ n) := by ring
    rwa [hid] at h
  -- cancel `V^n + c^n` (coprime to n² because `V^n+c^n ⋮̸ n`)
  have hcop : IsCoprime ((n : ℤ) ^ 2) (V ^ n + c ^ n) := by
    have hug : IsCoprime (V ^ n + c ^ n) (n : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (L5.L5_gcd_eq_one_of_not_dvd hn hc)
    exact hug.symm.pow_left (m := 2)
  exact Int.modEq_zero_iff_dvd.mpr (hcop.dvd_of_dvd_mul_left htarget)

/-- **S12** (author p. 5 §7, first bullet): "Vì c^n + b^n ≢ 0 (mod n),
b^{3n}+c^{3n} = (b^n+c^n)[(c^n−b^n)²+b^nc^n] ≡ (b^n+c^n)(a^{2n}+b^nc^n)
≡ 0 (mod n²) nên a^{2n}+b^nc^n ≡ 0 (mod n²)" — the printed chain, whose
`b^{3n}+c^{3n} ≡ 0 (mod n²)` is (19) from L7-FRAG-03. -/
theorem L7F4_step_S12 {n : ℕ} (hn : Nat.Prime n) {a b c : ℤ}
    (h19 : (b ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n ^ 2 : ℤ)])
    (hc : ¬ (n : ℤ) ∣ b ^ n + c ^ n) :
    (a ^ (2 * n) + b ^ n * c ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] :=
  L7F4_sum_chain hn (U := a) (V := b) h19 h1 hc

/-- **S13** (author p. 5 §7, first bullet, "Chứng minh tương tự ta cũng có
b^{2n}+a^nc^n ≡ c^{2n}−a^nb^n ≡ 0 (mod n²)").

The first conjunct is `L7F4_sum_chain` at `(U, V) = (b, a)` — the same
argument at the pair `(a, c)`. The second is the *difference* form of the
same factorization, `a^{3n}−b^{3n} = (a^n−b^n)(a^{2n}+a^nb^n+b^{2n})`, whose
factor `a^n−b^n` is ≢ 0 mod `n` by the non-divisibility conclusion verified in
chunk L7-FRAG-01 (S5c); combined with `c^{2n} ≡ (a^n+b^n)²` it gives
`c^{2n}−a^nb^n ≡ a^{2n}+a^nb^n+b^{2n} ≡ 0`. -/
theorem L7F4_step_S13 {n : ℕ} (hn : Nat.Prime n) {a b c : ℤ}
    (h10 : (a ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h20 : (a ^ (3 * n) - b ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n ^ 2 : ℤ)])
    (hac : ¬ (n : ℤ) ∣ a ^ n + c ^ n)
    (hab : ¬ (n : ℤ) ∣ a ^ n - b ^ n) :
    (b ^ (2 * n) + a ^ n * c ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (c ^ (2 * n) - a ^ n * b ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have hA2 : (a ^ (2 * n) : ℤ) = (a ^ n) ^ 2 := by rw [Nat.mul_comm 2 n, pow_mul]
  have hB2 : (b ^ (2 * n) : ℤ) = (b ^ n) ^ 2 := by rw [Nat.mul_comm 2 n, pow_mul]
  have hA3 : (a ^ (3 * n) : ℤ) = (a ^ n) ^ 3 := by rw [Nat.mul_comm 3 n, pow_mul]
  have hB3 : (b ^ (3 * n) : ℤ) = (b ^ n) ^ 3 := by rw [Nat.mul_comm 3 n, pow_mul]
  -- the difference factorization, then cancel `a^n−b^n`
  have htriple : (a ^ (2 * n) + a ^ n * b ^ n + b ^ (2 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
    have hfac : (a ^ (3 * n) - b ^ (3 * n) : ℤ)
        = (a ^ n - b ^ n) * (a ^ (2 * n) + a ^ n * b ^ n + b ^ (2 * n)) := by
      rw [hA3, hB3, hA2, hB2]; ring
    have hd : (n ^ 2 : ℤ) ∣ (a ^ n - b ^ n) * (a ^ (2 * n) + a ^ n * b ^ n + b ^ (2 * n)) := by
      have h := Int.modEq_zero_iff_dvd.mp h20
      rwa [hfac] at h
    have hcop : IsCoprime ((n : ℤ) ^ 2) (a ^ n - b ^ n) := by
      have hug : IsCoprime (a ^ n - b ^ n) (n : ℤ) :=
        Int.isCoprime_iff_gcd_eq_one.mpr (L5.L5_gcd_eq_one_of_not_dvd hn hab)
      exact hug.symm.pow_left (m := 2)
    exact Int.modEq_zero_iff_dvd.mpr (hcop.dvd_of_dvd_mul_left hd)
  constructor
  · exact L7F4_sum_chain hn (U := b) (V := a) h10 (by simpa [add_comm] using h1) hac
  · -- "c^{2n} ≡ (a^n+b^n)² = (a^{2n}+a^nb^n+b^{2n}) + a^nb^n ≡ a^nb^n"
    have hsquare : (c ^ (2 * n) : ℤ) ≡ (a ^ n + b ^ n) ^ 2 [ZMOD (n ^ 2 : ℤ)] := by
      have h := h1.pow 2
      have hc2 : ((c ^ n) ^ 2 : ℤ) = c ^ (2 * n) := by rw [Nat.mul_comm 2 n, pow_mul]
      rwa [hc2] at h
    have hid : ((a ^ n + b ^ n) ^ 2 : ℤ)
        = (a ^ (2 * n) + a ^ n * b ^ n + b ^ (2 * n)) + a ^ n * b ^ n := by
      rw [hA2, hB2]; ring
    have hone : ((a ^ (2 * n) + a ^ n * b ^ n + b ^ (2 * n)) + a ^ n * b ^ n : ℤ)
        ≡ a ^ n * b ^ n [ZMOD (n ^ 2 : ℤ)] := by
      simpa using htriple.add_right (a ^ n * b ^ n)
    have hcb : (c ^ (2 * n) : ℤ) ≡ a ^ n * b ^ n [ZMOD (n ^ 2 : ℤ)] := by
      rw [hid] at hsquare
      exact hsquare.trans hone
    simpa using hcb.sub (Int.ModEq.refl (a ^ n * b ^ n))

/-- **S14** (author p. 5 §7, second bullet): "Ta có c^{2n}−a^nb^n ≡ 0 (mod n²)
⇒ c^n(a^n+b^n)−a^nb^n ≡ 0 (mod n²) (vì a^n+b^n ≡ c^n (mod n²))
⇒ c^na^n.1 + c^nb^n.1 − a^nb^n.1 ≡ 0 (mod n²)
⇒ c^na^nb^{n(n−1)} + c^nb^na^{n(n−1)} − a^nb^nc^{n(n−1)} ≡ 0 (mod n²)
(theo bổ đề 5d)) ⇒ b^{n(n−2)} + a^{n(n−2)} − c^{n(n−2)} ≡ 0 (mod n²) (đpcm)"
— the main proof's (22'). The last step is the cancellation of `a^nb^nc^n`,
which the author's `abc ≢ 0 (mod n)` makes invertible mod `n²`. -/
theorem L7F4_step_S14 {n : ℕ} (hn : Nat.Prime n) {a b c : ℤ}
    (h13 : (c ^ (2 * n) - a ^ n * b ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n ^ 2 : ℤ)])
    (ha1 : (a ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)])
    (hb1 : (b ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)])
    (hc1 : (c ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)])
    (ha : ¬ (n : ℤ) ∣ a) (hb : ¬ (n : ℤ) ∣ b) (hc : ¬ (n : ℤ) ∣ c) :
    (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ)
      ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  -- "c^{2n} ≡ c^n(a^n+b^n)"
  have hcs : (c ^ (2 * n) : ℤ) ≡ c ^ n * (a ^ n + b ^ n) [ZMOD (n ^ 2 : ℤ)] := by
    have h := h1.mul_left (c ^ n)
    have hid : (c ^ n * c ^ n : ℤ) = c ^ (2 * n) := by
      rw [← pow_add, show n + n = 2 * n from by ring]
    rwa [hid] at h
  have hthree : (c ^ n * a ^ n + c ^ n * b ^ n - a ^ n * b ^ n : ℤ)
      ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
    have h0 : (n ^ 2 : ℤ) ∣ c ^ (2 * n) - a ^ n * b ^ n := Int.modEq_zero_iff_dvd.mp h13
    have hdiff : (n ^ 2 : ℤ) ∣
        (c ^ (2 * n) - a ^ n * b ^ n) - (c ^ n * (a ^ n + b ^ n) - a ^ n * b ^ n) := by
      have h := Int.modEq_iff_dvd.mp hcs.symm
      have hid : (c ^ (2 * n) - a ^ n * b ^ n) - (c ^ n * (a ^ n + b ^ n) - a ^ n * b ^ n)
          = c ^ (2 * n) - c ^ n * (a ^ n + b ^ n) := by ring
      rwa [hid]
    have hX : (n ^ 2 : ℤ) ∣ c ^ n * (a ^ n + b ^ n) - a ^ n * b ^ n := by
      have h := dvd_sub h0 hdiff
      have hid : (c ^ (2 * n) - a ^ n * b ^ n)
          - ((c ^ (2 * n) - a ^ n * b ^ n) - (c ^ n * (a ^ n + b ^ n) - a ^ n * b ^ n))
          = c ^ n * (a ^ n + b ^ n) - a ^ n * b ^ n := by ring
      rwa [hid] at h
    have hid : (c ^ n * (a ^ n + b ^ n) - a ^ n * b ^ n : ℤ)
        = c ^ n * a ^ n + c ^ n * b ^ n - a ^ n * b ^ n := by ring
    rw [hid] at hX
    exact Int.modEq_zero_iff_dvd.mpr hX
  -- 5d raises each of the three terms
  have hraised : (c ^ n * a ^ n * b ^ (n * (n - 1)) + c ^ n * b ^ n * a ^ (n * (n - 1))
      - a ^ n * b ^ n * c ^ (n * (n - 1)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
    have hd : ∀ x : ℤ, x ^ (n * (n - 1)) ≡ 1 [ZMOD (n ^ 2 : ℤ)] →
        (n ^ 2 : ℤ) ∣ x ^ (n * (n - 1)) - 1 := by
      intro x hx
      have h' := Int.modEq_iff_dvd.mp hx
      have h'' := dvd_neg.mpr h'
      rwa [neg_sub] at h''
    have hdiff : (n ^ 2 : ℤ) ∣
        (c ^ n * a ^ n * b ^ (n * (n - 1)) + c ^ n * b ^ n * a ^ (n * (n - 1))
          - a ^ n * b ^ n * c ^ (n * (n - 1)))
        - (c ^ n * a ^ n + c ^ n * b ^ n - a ^ n * b ^ n) := by
      have h1' : (n ^ 2 : ℤ) ∣ c ^ n * a ^ n * (b ^ (n * (n - 1)) - 1) :=
        dvd_mul_of_dvd_right (hd b hb1) _
      have h2' : (n ^ 2 : ℤ) ∣ c ^ n * b ^ n * (a ^ (n * (n - 1)) - 1) :=
        dvd_mul_of_dvd_right (hd a ha1) _
      have h3' : (n ^ 2 : ℤ) ∣ a ^ n * b ^ n * (c ^ (n * (n - 1)) - 1) :=
        dvd_mul_of_dvd_right (hd c hc1) _
      have h := dvd_sub (dvd_add h1' h2') h3'
      have hid : c ^ n * a ^ n * (b ^ (n * (n - 1)) - 1) + c ^ n * b ^ n * (a ^ (n * (n - 1)) - 1)
          - a ^ n * b ^ n * (c ^ (n * (n - 1)) - 1)
          = (c ^ n * a ^ n * b ^ (n * (n - 1)) + c ^ n * b ^ n * a ^ (n * (n - 1))
            - a ^ n * b ^ n * c ^ (n * (n - 1)))
          - (c ^ n * a ^ n + c ^ n * b ^ n - a ^ n * b ^ n) := by ring
      rwa [hid] at h
    have h0 : (n ^ 2 : ℤ) ∣ c ^ n * a ^ n + c ^ n * b ^ n - a ^ n * b ^ n :=
      Int.modEq_zero_iff_dvd.mp hthree
    have hfin : (n ^ 2 : ℤ) ∣ (c ^ n * a ^ n + c ^ n * b ^ n - a ^ n * b ^ n)
        + ((c ^ n * a ^ n * b ^ (n * (n - 1)) + c ^ n * b ^ n * a ^ (n * (n - 1))
            - a ^ n * b ^ n * c ^ (n * (n - 1)))
          - (c ^ n * a ^ n + c ^ n * b ^ n - a ^ n * b ^ n)) := dvd_add h0 hdiff
    have hid2 : (c ^ n * a ^ n + c ^ n * b ^ n - a ^ n * b ^ n)
        + ((c ^ n * a ^ n * b ^ (n * (n - 1)) + c ^ n * b ^ n * a ^ (n * (n - 1))
            - a ^ n * b ^ n * c ^ (n * (n - 1)))
          - (c ^ n * a ^ n + c ^ n * b ^ n - a ^ n * b ^ n))
        = c ^ n * a ^ n * b ^ (n * (n - 1)) + c ^ n * b ^ n * a ^ (n * (n - 1))
          - a ^ n * b ^ n * c ^ (n * (n - 1)) := by ring
    rw [hid2] at hfin
    exact Int.modEq_zero_iff_dvd.mpr hfin
  -- the product identity: that expression is `a^n b^n c^n · (target)`
  have haux : n + n * (n - 2) = n * (n - 1) := by
    have h2 : 2 ≤ n := hn.two_le
    rw [Nat.add_comm]
    rw [show n * (n - 2) + n = n * (n - 1) from by
      calc n * (n - 2) + n = n * (n - 2) + n * 1 := by rw [mul_one]
        _ = n * ((n - 2) + 1) := (Nat.mul_add n (n - 2) 1).symm
        _ = n * (n - 1) := by rw [show n - 2 + 1 = n - 1 from by omega]]
  have hA : (a ^ n * a ^ (n * (n - 2)) : ℤ) = a ^ (n * (n - 1)) := by
    rw [← pow_add, haux]
  have hB : (b ^ n * b ^ (n * (n - 2)) : ℤ) = b ^ (n * (n - 1)) := by
    rw [← pow_add, haux]
  have hC : (c ^ n * c ^ (n * (n - 2)) : ℤ) = c ^ (n * (n - 1)) := by
    rw [← pow_add, haux]
  have hprod : (c ^ n * a ^ n * b ^ (n * (n - 1)) + c ^ n * b ^ n * a ^ (n * (n - 1))
      - a ^ n * b ^ n * c ^ (n * (n - 1)) : ℤ)
      = a ^ n * b ^ n * c ^ n * (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2))) := by
    rw [← hA, ← hB, ← hC]; ring
  have hdvd : (n ^ 2 : ℤ) ∣ a ^ n * b ^ n * c ^ n
      * (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2))) := by
    have h := Int.modEq_zero_iff_dvd.mp hraised
    rwa [hprod] at h
  -- cancel `a^n b^n c^n` (coprime to n² because `a, b, c ⋮̸ n`)
  have hnd : ¬ (n : ℤ) ∣ a ^ n * b ^ n * c ^ n := by
    rintro h
    rcases Int.Prime.dvd_mul' hn h with h' | h'
    · rcases Int.Prime.dvd_mul' hn h' with h'' | h''
      · exact ha (Int.Prime.dvd_pow' hn h'')
      · exact hb (Int.Prime.dvd_pow' hn h'')
    · exact hc (Int.Prime.dvd_pow' hn h')
  have hcop : IsCoprime ((n : ℤ) ^ 2) (a ^ n * b ^ n * c ^ n) := by
    have hug : IsCoprime (a ^ n * b ^ n * c ^ n) (n : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (L5.L5_gcd_eq_one_of_not_dvd hn hnd)
    exact hug.symm.pow_left (m := 2)
  exact Int.modEq_zero_iff_dvd.mpr (hcop.dvd_of_dvd_mul_left hdvd)

end L7
