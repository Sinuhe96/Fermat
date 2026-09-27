import Mathlib
import L5.Basic
import L7F3.Basic

/-!
# Lemma 7 (bổ đề 7) — display (21) and (22) (chunk L7-FRAG-06)

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 2 top, the `a^{n(n−4)}` group and `a^{n(n−3)}+b^{n(n−3)}+c^{n(n−3)}`;
  * proof: p. 5 §7, the closing bullet ("Vì n ≡ 1 (mod 6) …").

The literal transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L7-FRAG-06.yml`:

  S18    "Vì n ≡ 1 (mod 6) … Do đó a^{n(n−4)}+c^{n(n−4)} = a^{3n(2p−1)} +
         (c^{3n})^{(2p−1)} ≡ a^{3n(2p−1)} − a^{3n(2p−1)} = 0 … suy ra
         a^{n(n−4)}+c^{n(n−4)} ≡ 0 (mod n²)"                  -> L7F6_step_S18
  S19    "Chứng minh tương tự ta cũng có: b^{n(n−4)}+c^{n(n−4)} ≡ 0 (mod n²)"
                                                              -> L7F6_step_S19
  S20    "suy ra a^{n(n−4)} − b^{n(n−4)} ≡ 0 (đpcm)"            -> L7F6_step_S20
  S21    (p. 2 display) "a^{n(n−3)}+b^{n(n−3)}+c^{n(n−3)} ≡ 0 (mod n²)" — (22)
                                                              -> L7F6_step_S21

## Encoding decisions

* `n % 6 = 1` ⟹ `n = 6l+1` ⟹ `n − 4 = 3·(2l−1)`; the two facts the printed
  computation uses are carried as the abstraction `n − 4 = 3·k` with `k` odd
  (the same device as `L7F5_step_S16` uses for `n − 2 = 3·(2l−1)`).
* The printed line derives the congruence mod `n` and then concludes mod `n²`;
  in fact the replacement `c^{3n} ≡ −a^{3n} (mod n²)` raised to the odd power
  `k` is a congruence mod `n²`, so the encoded statement is the mod-`n²` one
  (the display's (21), which is what the main proof cites).
* S20 is the printed "suy ra a^{n(n−4)}−b^{n(n−4)} ≡ 0" (printed mod `n`; the
  storage form (21) and the derivation are mod `n²`).
* S21 is (22): stated on p. 2 and used by the main proof at p. 30 R2
  ("Từ (17), (21), (22), ta có"), but not derived on p. 5. It is an F3
  fill-in from the author's own material — `a^{n(n−3)} = a^n·a^{n(n−4)}` with
  (21)'s `a^{n(n−4)} ≡ b^{n(n−4)} ≡ −c^{n(n−4)}` and (b) `c^n ≡ a^n+b^n`:
  the sum is `c^{n(n−4)}·(c^n − a^n − b^n) ≡ 0 (mod n²)`.
-/

namespace L7

/-- **S18** (author p. 5 §7, closing bullet): "Vì n ≡ 1 (mod 6), nên
n = 6l + 1, l ∈ ℕ*. Do đó a^{n(n−4)}+c^{n(n−4)} = a^{3n(2p−1)} +
(c^{3n})^{(2p−1)} ≡ a^{3n(2p−1)} − a^{3n(2p−1)} = 0 (mod n) (vì c^{3n} ≡ −a^{3n}
(mod n²)), suy ra a^{n(n−4)}+c^{n(n−4)} ≡ 0 (mod n²)".

The exponent `n − 4 = 3·(2l−1) = 3k` with `k` odd is what `n ≡ 1 (mod 6)`
supplies; `c^{3n} ≡ −a^{3n}` is (19). (The print's `p` is the same index as its
`l`.) -/
theorem L7F6_step_S18 {n k : ℕ} (hk : Odd k) (hnk : n - 4 = 3 * k) {a c : ℤ}
    (h19 : (a ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)]) :
    (a ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have hexp : 3 * n * k = n * (n - 4) := by rw [hnk]; ring
  have hpow : ∀ x : ℤ, ((x ^ (3 * n)) ^ k : ℤ) = x ^ (n * (n - 4)) := by
    intro x
    rw [← pow_mul, hexp]
  have hc : (c ^ (3 * n) : ℤ) ≡ (-(a ^ (3 * n))) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using h19.add_right (-(a ^ (3 * n)))
  have h := hc.pow k
  have hneg : ((-(a ^ (3 * n)) : ℤ)) ^ k = -((a ^ (3 * n)) ^ k) := Odd.neg_pow hk _
  rw [hneg, hpow a, hpow c] at h
  have hsum : (a ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ)
      ≡ a ^ (n * (n - 4)) + (-(a ^ (n * (n - 4)))) [ZMOD (n ^ 2 : ℤ)] :=
    (Int.ModEq.refl (a ^ (n * (n - 4)))).add h
  have hid : (a ^ (n * (n - 4)) + (-(a ^ (n * (n - 4)))) : ℤ) = 0 := by ring
  rwa [hid] at hsum

/-- **S19** (author p. 5 §7): "Chứng minh tương tự ta cũng có:
b^{n(n−4)}+c^{n(n−4)} ≡ 0 (mod n²)" — the same argument at the pair `(b, c)`
with (19)'s `b^{3n}+c^{3n} ≡ 0`. -/
theorem L7F6_step_S19 {n k : ℕ} (hk : Odd k) (hnk : n - 4 = 3 * k) {b c : ℤ}
    (h19 : (b ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)]) :
    (b ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have hexp : 3 * n * k = n * (n - 4) := by rw [hnk]; ring
  have hpow : ∀ x : ℤ, ((x ^ (3 * n)) ^ k : ℤ) = x ^ (n * (n - 4)) := by
    intro x
    rw [← pow_mul, hexp]
  have hc : (c ^ (3 * n) : ℤ) ≡ (-(b ^ (3 * n))) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using h19.add_right (-(b ^ (3 * n)))
  have h := hc.pow k
  have hneg : ((-(b ^ (3 * n)) : ℤ)) ^ k = -((b ^ (3 * n)) ^ k) := Odd.neg_pow hk _
  rw [hneg, hpow b, hpow c] at h
  have hsum : (b ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ)
      ≡ b ^ (n * (n - 4)) + (-(b ^ (n * (n - 4)))) [ZMOD (n ^ 2 : ℤ)] :=
    (Int.ModEq.refl (b ^ (n * (n - 4)))).add h
  have hid : (b ^ (n * (n - 4)) + (-(b ^ (n * (n - 4)))) : ℤ) = 0 := by ring
  rwa [hid] at hsum

/-- **S20** (author p. 5 §7): "suy ra a^{n(n−4)} − b^{n(n−4)} ≡ 0" — from the
two congruences of S18 and S19: both sums are `≡ 0`, so `a^{n(n−4)}` and
`b^{n(n−4)}` are both `≡ −c^{n(n−4)}`. -/
theorem L7F6_step_S20 {n : ℕ} {a b c : ℤ}
    (h18 : (a ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h19 : (b ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)]) :
    (a ^ (n * (n - 4)) - b ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have hca : (c ^ (n * (n - 4)) : ℤ) ≡ (-(a ^ (n * (n - 4)))) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using h18.add_right (-(a ^ (n * (n - 4))))
  have hcb : (c ^ (n * (n - 4)) : ℤ) ≡ (-(b ^ (n * (n - 4)))) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using h19.add_right (-(b ^ (n * (n - 4))))
  have hba : (b ^ (n * (n - 4)) : ℤ) ≡ a ^ (n * (n - 4)) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using (hcb.symm.trans hca).neg
  have h0 : (b ^ (n * (n - 4)) - b ^ (n * (n - 4)) : ℤ)
      ≡ a ^ (n * (n - 4)) - b ^ (n * (n - 4)) [ZMOD (n ^ 2 : ℤ)] :=
    hba.sub (Int.ModEq.refl (b ^ (n * (n - 4))))
  simpa using h0.symm

/-- **S21** (author p. 2, display (22)): "a^{n(n−3)} + b^{n(n−3)} + c^{n(n−3)}
≡ 0 (mod n²)" — the F3 fill-in recorded in the chunk YAML (the main proof
cites it at p. 30 R2 as (22); the printed proof derives (21) but not (22)).

Writing `a^{n(n−3)} = a^n·a^{n(n−4)}` and using (21)'s
`a^{n(n−4)} ≡ b^{n(n−4)} ≡ −c^{n(n−4)}` together with (b)
`c^n ≡ a^n + b^n (mod n²)`, the sum is `c^{n(n−4)}·(c^n − a^n − b^n) ≡ 0`. -/
theorem L7F6_step_S21 {n : ℕ} (h3 : 3 < n) {a b c : ℤ}
    (h18 : (a ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h19 : (b ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n ^ 2 : ℤ)]) :
    (a ^ (n * (n - 3)) + b ^ (n * (n - 3)) + c ^ (n * (n - 3)) : ℤ)
      ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have ha : (a ^ (n * (n - 4)) : ℤ) ≡ (-(c ^ (n * (n - 4)))) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using h18.add_right (-(c ^ (n * (n - 4))))
  have hb : (b ^ (n * (n - 4)) : ℤ) ≡ (-(c ^ (n * (n - 4)))) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using h19.add_right (-(c ^ (n * (n - 4))))
  have haux : n + n * (n - 4) = n * (n - 3) := by
    have h4 : 4 ≤ n := by omega
    rw [Nat.add_comm]
    rw [show n * (n - 4) + n = n * (n - 3) from by
      calc n * (n - 4) + n = n * (n - 4) + n * 1 := by rw [mul_one]
        _ = n * ((n - 4) + 1) := (Nat.mul_add n (n - 4) 1).symm
        _ = n * (n - 3) := by rw [show n - 4 + 1 = n - 3 from by omega]]
  have hA : (a ^ n * a ^ (n * (n - 4)) : ℤ) = a ^ (n * (n - 3)) := by
    rw [← pow_add, haux]
  have hB : (b ^ n * b ^ (n * (n - 4)) : ℤ) = b ^ (n * (n - 3)) := by
    rw [← pow_add, haux]
  have hC : (c ^ n * c ^ (n * (n - 4)) : ℤ) = c ^ (n * (n - 3)) := by
    rw [← pow_add, haux]
  have hcomb : (a ^ n * (-(c ^ (n * (n - 4)))) + b ^ n * (-(c ^ (n * (n - 4))))
      + (a ^ n + b ^ n) * c ^ (n * (n - 4)) : ℤ) = 0 := by ring
  have hsum : (a ^ n * a ^ (n * (n - 4)) + b ^ n * b ^ (n * (n - 4))
      + c ^ n * c ^ (n * (n - 4)) : ℤ)
      ≡ (a ^ n * (-(c ^ (n * (n - 4)))) + b ^ n * (-(c ^ (n * (n - 4))))
          + (a ^ n + b ^ n) * c ^ (n * (n - 4))) [ZMOD (n ^ 2 : ℤ)] :=
    ((ha.mul_left (a ^ n)).add (hb.mul_left (b ^ n))).add
      (h1.mul_right (c ^ (n * (n - 4))))
  rw [hcomb] at hsum
  rw [← hA, ← hB, ← hC]
  exact hsum

end L7
