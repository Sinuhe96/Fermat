import Mathlib
import L5.Basic

/-!
# Lemma 7 (bổ đề 7) — display (a) and the (b), (c), (d) toolkit (chunk L7-FRAG-02)

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 1 bottom → p. 2 top, lemma 7 of section A (display (a) and
    the congruences (b), (c), (d) every other conclusion group builds on);
  * proof: p. 4 bottom → p. 5, "7. Chứng minh bổ đề 7".

The literal transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L7-FRAG-02.yml`. One named declaration per author
step (English paraphrase); this is the author's own chain, in his order:

  S0     5d at a, b, c: x^{n(n−1)} ≡ 1 (mod n²)              -> L7F2_step_S0
  S1     the printed identity
         a^{n²}+b^{n²}−c^{n²} = (a^n+b^n−c^n) − c^n[c^{n(n−1)}−1]
             + a^n[a^{n(n−1)}−1] + b^n[b^{n(n−1)}−1] ≡ 0 (mod n²)
         ⇒ (a)                                                 -> L7F2_step_S1
  S2     (b) c^n ≡ a^n+b^n (mod n²), (c) c^{n(n−2)} ≡ …      -> L7F2_step_S2
  S3     "nhân hai vế của (c) cho a^nb^nc^n", then 5d          -> L7F2_step_S3
  S4     (d) a^n b^n ≡ c^{2n} (mod n)                         -> L7F2_step_S4

## Encoding decisions

* Modulus spelling: `(n ^ 2 : ℤ)` and the `(↑n) ^ 2` that bổ đề 5's statements
  display are the *same* term (the ascription forces the power to be taken in
  `ℤ`), so no cast bridge between the two chunks is needed.
* S0 is bổ đề 5d (`L5_step_S17` → `L5_step_S18`) at the author's three
  coordinates; `Odd n` comes from `n` prime with `3 < n`.
* S1 is the printed identity; its four summands are each `≡ 0 (mod n²)` —
  the first by GT2, the other three by 5d (S0) — so the statement is a
  congruence, not a division.
* S3 multiplies (c) by `a^n b^n c^n` (`Int.ModEq.mul`) and uses 5d at modulus
  `n`; the resulting `a^n b^n ≡ c^n (a^n + b^n) (mod n)` is then read through
  (b) at modulus `n` in S4 to give the printed (d).
-/

namespace L7

/-- **S0** (author p. 4, first line of the §7 proof): "Vì abc ≢ 0 (mod n), nên
a ≢ 0, b ≢ 0, c ≢ 0 (mod n), vì vậy theo bổ đề 5d), ta có:
c^{n(n−1)} ≡ a^{n(n−1)} ≡ b^{n(n−1)} ≡ 1 (mod n²)".

Bổ đề 5d at the three coordinates (bổ đề 5's own step `S17 → S18`), the
`Odd n` it needs coming from `n` prime with `3 < n`. -/
theorem L7F2_step_S0 {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n) {a b c : ℤ}
    (ha : ¬ (n : ℤ) ∣ a) (hb : ¬ (n : ℤ) ∣ b) (hc : ¬ (n : ℤ) ∣ c) :
    a ^ (n * (n - 1)) ≡ 1 [ZMOD (n ^ 2 : ℤ)] ∧
      b ^ (n * (n - 1)) ≡ 1 [ZMOD (n ^ 2 : ℤ)] ∧
      c ^ (n * (n - 1)) ≡ 1 [ZMOD (n ^ 2 : ℤ)] := by
  have hodd : Odd n := hn.odd_of_ne_two (by omega)
  have key : ∀ u : ℤ, ¬ (n : ℤ) ∣ u → u ^ (n * (n - 1)) ≡ 1 [ZMOD (n ^ 2 : ℤ)] := by
    intro u hu
    obtain ⟨m, hm⟩ := L5.L5_step_S17 hn hodd hu
    simpa using L5.L5_step_S18 hm
  exact ⟨key a ha, key b hb, key c hc⟩

/-- **S2** (author p. 4 §7): the two displayed congruences
"(b) c^n ≡ a^n + b^n (mod n²)" and "(c) c^{n(n−2)} ≡ a^{n(n−2)} + b^{n(n−2)}
(mod n)" — GT2 and GT3 rearranged. -/
theorem L7F2_step_S2 {n : ℕ} {a b c : ℤ}
    (h2 : (a ^ n + b ^ n - c ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h3 : (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ)
      ≡ 0 [ZMOD (n : ℤ)]) :
    (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n ^ 2 : ℤ)] ∧
      (c ^ (n * (n - 2)) : ℤ) ≡ a ^ (n * (n - 2)) + b ^ (n * (n - 2))
        [ZMOD (n : ℤ)] := by
  refine ⟨?_, ?_⟩
  · exact Int.modEq_iff_dvd.mpr (Int.modEq_zero_iff_dvd.mp h2)
  · exact Int.modEq_iff_dvd.mpr (Int.modEq_zero_iff_dvd.mp h3)

/-- **S1** (author p. 4 §7 → p. 5): the printed identity

  a^{n²}+b^{n²}−c^{n²} = (a^n+b^n−c^n) − c^n[c^{n(n−1)}−1] + a^n[a^{n(n−1)}−1]
                          + b^n[b^{n(n−1)}−1] ≡ 0 (mod n²)

"⇒ a^{n²}+b^{n²}−c^{n²} ≡ 0 (mod n²) (a)": the first summand is GT2, the other
three are divisible by `n²` by 5d (S0, each `x^{n(n−1)} ≡ 1`). The identity is
an algebraic identity, so the step is a congruence, not a division. -/
theorem L7F2_step_S1 {n : ℕ} (hn : Nat.Prime n) {a b c : ℤ}
    (h2 : (a ^ n + b ^ n - c ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (ha1 : (a ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)])
    (hb1 : (b ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)])
    (hc1 : (c ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)]) :
    (a ^ (n ^ 2) + b ^ (n ^ 2) - c ^ (n ^ 2) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have hexp : n ^ 2 = n + n * (n - 1) := by
    have hsucc : n * (n - 1) + n = n * n := by
      calc n * (n - 1) + n = n * (n - 1) + n * 1 := by rw [mul_one]
        _ = n * ((n - 1) + 1) := (Nat.mul_add n (n - 1) 1).symm
        _ = n * n := by rw [Nat.sub_one_add_one_eq_of_pos hn.pos]
    rw [pow_two, Nat.add_comm, hsucc]
  have hpow : ∀ x : ℤ, x ^ (n ^ 2) = x ^ n * x ^ (n * (n - 1)) := by
    intro x
    rw [hexp, pow_add]
  have hid : (a ^ (n ^ 2) + b ^ (n ^ 2) - c ^ (n ^ 2) : ℤ)
      = (a ^ n + b ^ n - c ^ n) - c ^ n * (c ^ (n * (n - 1)) - 1)
        + a ^ n * (a ^ (n * (n - 1)) - 1) + b ^ n * (b ^ (n * (n - 1)) - 1) := by
    rw [hpow a, hpow b, hpow c]; ring
  rw [hid]
  have hdvd : ∀ x y : ℤ, x ^ (n * (n - 1)) ≡ 1 [ZMOD (n ^ 2 : ℤ)] →
      (n ^ 2 : ℤ) ∣ y * (x ^ (n * (n - 1)) - 1) := by
    intro x y hx
    have h : (n ^ 2 : ℤ) ∣ x ^ (n * (n - 1)) - 1 := by
      have h' := Int.modEq_iff_dvd.mp hx
      have h'' := dvd_neg.mpr h'
      rwa [neg_sub] at h''
    exact dvd_mul_of_dvd_right h y
  have hd1 : (n ^ 2 : ℤ) ∣ a ^ n + b ^ n - c ^ n := Int.modEq_zero_iff_dvd.mp h2
  exact Int.modEq_zero_iff_dvd.mpr
    (dvd_add (dvd_add (dvd_sub hd1 (hdvd c (c ^ n) hc1)) (hdvd a (a ^ n) ha1))
      (hdvd b (b ^ n) hb1))

/-- **S3** (author p. 4 → p. 5 §7): "Từ (c) suy ra
c^{n(n−1)}a^nb^n ≡ a^{n(n−1)}c^nb^n + b^{n(n−1)}c^na^n (mod n) (nhân hai vế
của đồng dư thức (c) cho a^nb^nc^n ≢ 0 (mod n)) ⇒ a^nb^n ≡ c^n(a^n+b^n) (mod n)".

The multiplication by `a^nb^nc^n` and the collapse of the three `x^{n(n−1)}`
factors by 5d (S0) are encoded through the 5d congruences directly. The (c)
input is at modulus `n` — that is the modulus the printed (c) itself has, and
the modulus this step works at; the 5d inputs come from S0 at modulus `n²` and
are reduced to `n` inside the proof. -/
theorem L7F2_step_S3 {n : ℕ} (hn : Nat.Prime n) {a b c : ℤ}
    (hc : (c ^ (n * (n - 2)) : ℤ) ≡ a ^ (n * (n - 2)) + b ^ (n * (n - 2))
      [ZMOD (n : ℤ)])
    (ha1 : (a ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)])
    (hb1 : (b ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)])
    (hc1 : (c ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)]) :
    (a ^ n * b ^ n : ℤ) ≡ c ^ n * (a ^ n + b ^ n) [ZMOD (n : ℤ)] := by
  have hred : ∀ {x y : ℤ}, x ≡ y [ZMOD (n ^ 2 : ℤ)] → x ≡ y [ZMOD (n : ℤ)] := fun h =>
    Int.ModEq.of_dvd (dvd_pow_self (n : ℤ) (by norm_num)) h
  have hc1' : (c ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n : ℤ)] := hred hc1
  have ha1' : (a ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n : ℤ)] := hred ha1
  have hb1' : (b ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n : ℤ)] := hred hb1
  have h2n : 2 ≤ n := hn.two_le
  have hexp' : n * (n - 2) + n = n * (n - 1) := by
    calc n * (n - 2) + n = n * (n - 2) + n * 1 := by rw [mul_one]
      _ = n * ((n - 2) + 1) := (Nat.mul_add n (n - 2) 1).symm
      _ = n * (n - 1) := by rw [show n - 2 + 1 = n - 1 from by omega]
  have hexp : n + n * (n - 2) = n * (n - 1) := by rw [Nat.add_comm, hexp']
  have hA : (a ^ n * a ^ (n * (n - 2)) : ℤ) = a ^ (n * (n - 1)) := by
    rw [← pow_add, hexp]
  have hB : (b ^ n * b ^ (n * (n - 2)) : ℤ) = b ^ (n * (n - 1)) := by
    rw [← pow_add, hexp]
  have hC : (c ^ n * c ^ (n * (n - 2)) : ℤ) = c ^ (n * (n - 1)) := by
    rw [← pow_add, hexp]
  -- "nhân hai vế của (c) cho a^n b^n c^n"
  have hmul := hc.mul (Int.ModEq.refl (a ^ n * b ^ n * c ^ n))
  have hidL : (c ^ (n * (n - 2)) * (a ^ n * b ^ n * c ^ n) : ℤ)
      = a ^ n * b ^ n * c ^ (n * (n - 1)) := by
    rw [show (c ^ (n * (n - 2)) * (a ^ n * b ^ n * c ^ n) : ℤ)
      = (c ^ (n * (n - 2)) * c ^ n) * (a ^ n * b ^ n) by ring]
    rw [← pow_add, hexp']
    ring
  -- the three 5d collapses
  have hL : (c ^ (n * (n - 2)) * (a ^ n * b ^ n * c ^ n) : ℤ)
      ≡ a ^ n * b ^ n [ZMOD (n : ℤ)] := by
    rw [hidL]
    simpa using hc1'.mul_left (a ^ n * b ^ n)
  have hidR : ((a ^ (n * (n - 2)) + b ^ (n * (n - 2))) * (a ^ n * b ^ n * c ^ n) : ℤ)
      = a ^ (n * (n - 1)) * b ^ n * c ^ n + b ^ (n * (n - 1)) * a ^ n * c ^ n := by
    rw [← hA, ← hB]; ring
  have hR : ((a ^ (n * (n - 2)) + b ^ (n * (n - 2))) * (a ^ n * b ^ n * c ^ n) : ℤ)
      ≡ c ^ n * (a ^ n + b ^ n) [ZMOD (n : ℤ)] := by
    rw [hidR]
    have h1 : (a ^ (n * (n - 1)) * b ^ n * c ^ n : ℤ) ≡ b ^ n * c ^ n [ZMOD (n : ℤ)] := by
      simpa [mul_assoc] using ha1'.mul_right (b ^ n * c ^ n)
    have h2 : (b ^ (n * (n - 1)) * a ^ n * c ^ n : ℤ) ≡ a ^ n * c ^ n [ZMOD (n : ℤ)] := by
      simpa [mul_assoc] using hb1'.mul_right (a ^ n * c ^ n)
    have hfin : (b ^ n * c ^ n + a ^ n * c ^ n : ℤ) = c ^ n * (a ^ n + b ^ n) := by ring
    exact (h1.add h2).trans (by rw [hfin])
  exact hL.symm.trans (hmul.trans hR)

/-- **S4** (author p. 5 §7): "⇒ a^nb^n ≡ c^{2n} (mod n) (d) (vì a^n+b^n ≡ c^n
(mod n²))" — (b) read at modulus `n` replaces `a^n+b^n` by `c^n` in S3's
conclusion. -/
theorem L7F2_step_S4 {n : ℕ} {a b c : ℤ}
    (h3 : (a ^ n * b ^ n : ℤ) ≡ c ^ n * (a ^ n + b ^ n) [ZMOD (n : ℤ)])
    (h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n ^ 2 : ℤ)]) :
    (a ^ n * b ^ n : ℤ) ≡ c ^ (2 * n) [ZMOD (n : ℤ)] := by
  have hred : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n : ℤ)] :=
    Int.ModEq.of_dvd (dvd_pow_self (n : ℤ) (by norm_num)) h1
  have h : (c ^ n * (a ^ n + b ^ n) : ℤ) ≡ c ^ n * c ^ n [ZMOD (n : ℤ)] :=
    hred.symm.mul_left (c ^ n)
  have hc2 : (c ^ n * c ^ n : ℤ) = c ^ (2 * n) := by
    rw [← pow_add, show n + n = 2 * n from by ring]
  rw [hc2] at h
  exact h3.trans h

end L7
