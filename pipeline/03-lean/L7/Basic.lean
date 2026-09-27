import Mathlib
import L5.Basic

/-!
# Lemma 7 (bổ đề 7) — non-divisibility conclusion (chunk L7-FRAG-01)

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 1 bottom → p. 2 top, lemma 7 of section A;
  * proof: p. 4 bottom → p. 5 top, "7. Chứng minh bổ đề 7".

The literal Vietnamese transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L7-FRAG-01.yml` (`source_text`, `author_steps`).
One named declaration per author step (English paraphrase):

  S0     abc ≢ 0 (mod n) ⇒ a, b, c ≢ 0 (mod n)              -> L7_step_S0
  S1     (b) c^n ≡ a^n + b^n (mod n²), reduced mod n        -> L7_step_S1
  S2     (c) c^{n(n−2)} ≡ a^{n(n−2)} + b^{n(n−2)} (mod n)   -> L7_step_S2
  S3+S4  "Nếu b^n + c^n ≡ 0 (mod n)" ⇒ c^n ≡ −b^n ⇒
         a^n ≡ −2b^n ⇒ a^{n(n−2)} + 2b^{n(n−2)} ≡ 0 ⇒
         −2^{n−2} + 2 ≡ 0 ⇒ −(2^{n−1} − 1) + 3 ≡ 0 ⇒ 3 ≡ 0 ⇒ n = 3,
         vô lý; "Vậy b^n + c^n ≢ 0 (mod n)"                 -> L7_step_S3_S4
         (the shared chain of that reductio: L7_pair_reductio)
  S5a    "Chứng minh tương tự ta cũng có a^n + b^n ≢ 0"     -> L7_step_S5a
  S5b    "… c^n + a^n ≢ 0 (mod n)"                          -> L7_step_S5b
  S5c    "… a^n − b^n ≢ 0 (mod n)" — not in the printed
         "tương tự" list, but required by the printed statement's
         product; the author's own "Lưu ý" symmetry makes it the
         printed reductio at `(X, Y, Z) = (−b, a, c)`               -> L7_step_S5c
  S6     "Tóm lại, ta luôn có (a^n − b^n)(c^n + a^n)(c^n + b^n) ≢ 0 (mod n)"
                                                                    -> L7_step_S6

## Encoding decisions

* S0–S2 are `ZMod n` statements (S1/S2 turn the two congruences GT2/GT3 into
  the `ZMod n` equalities the earlier draft's reductio consumed); they are
  kept verbatim from the first verified rounds. The reductio S3–S5 is carried
  out in **ℤ congruence/divisibility** form instead, which is the author's own
  modulus arithmetic ("c^n ≡ −b^n", "−2^{n−2} + 2 ≡ 0", …) and the form this
  repository's verified chunks use for mod-n arguments. `L7_modEq_of_zmod_eq`
  converts S1/S2's output into the `Int.ModEq` hypotheses the reductio takes.
* S0's record note "cites bổ đề 5đ" was ours, not the print's: the step needs
  no cited lemma and no primality (`n ∣ a ⇒ n ∣ abc`). Corrected in the YAML.
* The printed reductio is written once, for `b^n + c^n`, and the other two
  instances are dismissed with "chứng minh tương tự". `L7_pair_reductio` is
  that same chain with the pair `(X, Y)` and the third variable `Z` abstracted,
  so S3+S4 and S5b are literal instantiations of the author's argument — the
  abstraction is the print's own claim of analogy, not new mathematics.
* S5a is not the b^n + c^n chain (that chain is vacuous for this pair): it is
  the contradiction the print's own material gives, recorded as an F3 fill-in
  in the chunk YAML — if `a^n + b^n ≡ 0` then (b) makes `c^n ≡ 0`, so
  `n ∣ c^n` and, `n` being prime, `n ∣ c`, contradicting S0's `c ≢ 0 (mod n)`.
* S5c is the one instance the printed "chứng minh tương tự" line leaves out
  (the print lists the three pairwise sums), while the statement's product —
  and the main proof's own use of the lemma — needs the difference
  `a^n − b^n ≢ 0`. It is still the author's own argument, not ours: the
  lemma's "Lưu ý" paragraph states that the hypotheses (b)/(c) are symmetric
  under the pairs `(a; b)`, `(c; −a)`, `(c; −b)`, and at `(X, Y, Z) = (−b, a, c)`
  the printed reductio `L7_pair_reductio` has exactly (b) and (c) as inputs
  (`n` odd turns `c^n ≡ a^n + b^n` into `Y^n ≡ Z^n + X^n`) and concludes
  `¬ n ∣ a^n − b^n`. Recorded as an F3 fill-in in the chunk YAML, with the
  downstream evidence (main proof p. 32, display (27)) that the difference is
  the intended reading — author query Q-001 is answered by that evidence.
* The import of `L5.Basic` is this chunk's declared dependency
  (`depends_on: [L5-01]`): bổ đề 7's *other* printed conclusions (displays (a)
  and (d), the b^{3n}+c^{3n} chain) rest on bổ đề 5c/5đ via
  `L5_bo_de_5`'s conjuncts `.2.2.1`/`.2.2.2`; the tail below reuses bổ đề 5's
  `L5_gcd_eq_one_of_not_dvd` for Fermat's little theorem in the form the
  author cites it (`2^{n−1} ≡ 1 (mod n)`).
-/

namespace L7

/-- Plumbing bridge: the print's (b)/(c) are congruences mod `n`; S1/S2 state
them as `ZMod n` equalities, and the reductio consumes them as `Int.ModEq`
facts in ℤ. -/
lemma L7_modEq_of_zmod_eq {n : ℕ} {x y : ℤ} (h : (x : ZMod n) = (y : ZMod n)) :
    x ≡ y [ZMOD (n : ℤ)] := by
  refine (Int.modEq_iff_dvd).mpr ?_
  have h0 : ((y - x : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [h]
    exact sub_self _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y - x) n).mp h0

/-- The author's shared tail (p. 5), printed once inside the `b^n + c^n`
reductio and reused verbatim by its symmetric instances:

  "Nên −2^{n−2} + 2 ≡ 0 (mod n) ⇒ −(2^{n−1} − 1) + 3 ≡ 0 (mod n).
   Mà theo định lý nhỏ Fermat: 2^{n−1} ≡ 1 (mod n)
   ⇒ 3 ≡ 0 (mod n) ⇒ n = 3, vô lý."

Input is the cancellation line `2^{n−2} ≡ 2 (mod n)`; the contradiction is
with the statement's `n > 3`. Fermat's little theorem is bổ đề 5's
`Int.ModEq.pow_card_sub_one_eq_one` (reused), applied at `2` with
`(2, n) = 1` supplied by `L5_gcd_eq_one_of_not_dvd`. -/
lemma L7_tail_three {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n)
    (h22 : (2 : ℤ) ^ (n - 2) ≡ 2 [ZMOD (n : ℤ)]) : False := by
  have hnot2 : ¬ (n : ℤ) ∣ (2 : ℤ) := by
    intro h
    have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) (Int.natCast_dvd_natCast.mp h)
    omega
  have hflt : (2 : ℤ) ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)] :=
    Int.ModEq.pow_card_sub_one_eq_one hn
      (Int.isCoprime_iff_gcd_eq_one.mpr (L5.L5_gcd_eq_one_of_not_dvd hn hnot2))
  -- "−2^{n−2} + 2 ≡ 0" and "2^{n−1} − 1 ≡ 0" together give "3 ≡ 0"
  have hd22 : (n : ℤ) ∣ 2 - 2 ^ (n - 2) := Int.modEq_iff_dvd.mp h22
  have hdflt : (n : ℤ) ∣ 2 ^ (n - 1) - 1 := hflt.symm.dvd
  have hd3' : (n : ℤ) ∣ (2 * (2 - 2 ^ (n - 2)) + (2 ^ (n - 1) - 1) : ℤ) :=
    dvd_add (dvd_mul_of_dvd_right hd22 2) hdflt
  have hid : (2 * (2 - 2 ^ (n - 2)) + (2 ^ (n - 1) - 1) : ℤ) = 3 := by
    rw [show n - 1 = (n - 2) + 1 from by omega, pow_succ]
    ring
  have hd3 : (n : ℤ) ∣ 3 := by
    rwa [hid] at hd3'
  -- "⇒ n = 3, vô lý" (against `h3 : 3 < n`)
  have hle3 : n ≤ 3 := Nat.le_of_dvd (by norm_num) (Int.natCast_dvd_natCast.mp hd3)
  omega

/-- The author's reductio (p. 4 bottom → p. 5), with the pair `(X, Y)` and the
third variable `Z` abstracted — sub-step by sub-step (chunk YAML S3a–S3i):

  S3a  "thì c^n ≡ −b^n"                    -> `hY : Y^n ≡ −X^n`
  S3b  "kết hợp với (b)": a^n ≡ c^n − b^n ≡ −2b^n
                                           -> `hZ : Z^n ≡ −2·X^n`
  S3c  "và (c)": (−b^n)^{n−2} ≡ a^e + b^e  -> `hYpow`
  S3d  "(vì n lẻ)": (−b^n)^{n−2} = −b^e, so a^e + 2b^e ≡ 0
                                           -> `hneg`, `hstep1`
  S3e  a^e = (a^n)^{n−2} ≡ (−2b^n)^{n−2}   -> `hZpow`, `hstep2`
  S3f  (−2b^n)^{n−2} = −2^{n−2}·b^e        -> `hpow`, `hstep3`, `hfac`
  S3g  "(vì b ≢ 0)": −2^{n−2} + 2 ≡ 0      -> `hX`, `hA`, `h22`
  S3h  + S3i (Fermat, 3 ≡ 0, n = 3 absurd) -> `L7_tail_three`

The print states this chain for `(X, Y, Z) = (b, c, a)`; the symmetric
`c^n + a^n` instance is the same chain at `(c, a, b)`, which is what the
author means by "chứng minh tương tự". -/
lemma L7_pair_reductio {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n) {X Y Z : ℤ}
    (hX : ¬ (n : ℤ) ∣ X)
    (h1 : Y ^ n ≡ Z ^ n + X ^ n [ZMOD (n : ℤ)])
    (h2 : Y ^ (n * (n - 2)) ≡ Z ^ (n * (n - 2)) + X ^ (n * (n - 2)) [ZMOD (n : ℤ)]) :
    ¬ (n : ℤ) ∣ X ^ n + Y ^ n := by
  have hodd2 : Odd (n - 2) := by
    obtain ⟨k, hk⟩ := hn.odd_of_ne_two (by omega)
    exact ⟨k - 1, by omega⟩
  intro hdvd
  -- S3a: "thì c^n ≡ −b^n", i.e. Y^n ≡ −X^n
  have hY : (Y ^ n : ℤ) ≡ -(X ^ n) [ZMOD (n : ℤ)] := by
    refine (Int.modEq_iff_dvd).mpr ?_
    have hid : -(X ^ n) - Y ^ n = -(X ^ n + Y ^ n) := by ring
    rw [hid]
    exact dvd_neg.mpr hdvd
  -- S3b: "kết hợp với (b)": Z^n ≡ −2·X^n
  have hZ : (Z ^ n : ℤ) ≡ -(2 * X ^ n) [ZMOD (n : ℤ)] := by
    refine (Int.modEq_iff_dvd).mpr ?_
    have ha : (n : ℤ) ∣ -(X ^ n) - Y ^ n := Int.modEq_iff_dvd.mp hY
    have hb : (n : ℤ) ∣ (Z ^ n + X ^ n) - Y ^ n := Int.modEq_iff_dvd.mp h1
    have h := dvd_sub ha hb
    have hid : (-(X ^ n) - Y ^ n) - ((Z ^ n + X ^ n) - Y ^ n) = -(2 * X ^ n) - Z ^ n := by
      ring
    rwa [hid] at h
  -- S3c: "và (c)": (−X^n)^{n−2} ≡ Z^e + X^e
  have hYpow : (-(X ^ n) : ℤ) ^ (n - 2) ≡ Z ^ (n * (n - 2)) + X ^ (n * (n - 2))
      [ZMOD (n : ℤ)] := by
    have h := hY.pow (n - 2)
    rw [← pow_mul] at h
    exact h.symm.trans h2
  -- S3d: "(vì n lẻ)": (−X^n)^{n−2} = −X^e, hence Z^e + 2·X^e ≡ 0
  have hneg : (-(X ^ n) : ℤ) ^ (n - 2) = -(X ^ (n * (n - 2))) := by
    rw [Odd.neg_pow hodd2, pow_mul]
  have hstep1 : (n : ℤ) ∣ Z ^ (n * (n - 2)) + 2 * X ^ (n * (n - 2)) := by
    have h : (-(X ^ (n * (n - 2)))) ≡ Z ^ (n * (n - 2)) + X ^ (n * (n - 2))
        [ZMOD (n : ℤ)] := by
      rw [← hneg]
      exact hYpow
    have hd := Int.modEq_iff_dvd.mp h
    have hid : (Z ^ (n * (n - 2)) + X ^ (n * (n - 2))) - (-(X ^ (n * (n - 2))))
        = Z ^ (n * (n - 2)) + 2 * X ^ (n * (n - 2)) := by ring
    rwa [hid] at hd
  -- S3e: a^e = (a^n)^{n−2} ≡ (−2b^n)^{n−2} — substituted into S3d
  have hZpow : (Z ^ (n * (n - 2)) : ℤ) ≡ (-(2 * X ^ n)) ^ (n - 2) [ZMOD (n : ℤ)] := by
    have h := hZ.pow (n - 2)
    rw [← pow_mul] at h
    exact h
  have hstep2 : (n : ℤ) ∣ (-(2 * X ^ n)) ^ (n - 2) + 2 * X ^ (n * (n - 2)) := by
    have hC : (n : ℤ) ∣ (-(2 * X ^ n)) ^ (n - 2) - Z ^ (n * (n - 2)) :=
      Int.modEq_iff_dvd.mp hZpow
    have hsum := dvd_add hstep1 hC
    have hid : (Z ^ (n * (n - 2)) + 2 * X ^ (n * (n - 2)))
        + ((-(2 * X ^ n)) ^ (n - 2) - Z ^ (n * (n - 2)))
        = (-(2 * X ^ n)) ^ (n - 2) + 2 * X ^ (n * (n - 2)) := by ring
    rwa [hid] at hsum
  -- S3f: (−2b^n)^{n−2} = −2^{n−2}·b^e, hence (2 − 2^{n−2})·b^e ≡ 0
  have hpow : (-(2 * X ^ n) : ℤ) ^ (n - 2) = -(2 ^ (n - 2) * X ^ (n * (n - 2))) := by
    rw [Odd.neg_pow hodd2, mul_pow, ← pow_mul]
  have hstep3 : (n : ℤ) ∣
      -(2 ^ (n - 2) * X ^ (n * (n - 2))) + 2 * X ^ (n * (n - 2)) := by
    rw [hpow] at hstep2
    exact hstep2
  have hfac : (n : ℤ) ∣ (2 - 2 ^ (n - 2)) * X ^ (n * (n - 2)) := by
    have hid : -(2 ^ (n - 2) * X ^ (n * (n - 2))) + 2 * X ^ (n * (n - 2))
        = (2 - 2 ^ (n - 2)) * X ^ (n * (n - 2)) := by ring
    rwa [hid] at hstep3
  -- S3g: "(vì b ≢ 0)" cancels b^e; then the author's shared tail
  have hA : (n : ℤ) ∣ 2 - 2 ^ (n - 2) := by
    have hXe : ¬ (n : ℤ) ∣ X ^ (n * (n - 2)) := fun h => hX (Int.Prime.dvd_pow' hn h)
    rcases Int.Prime.dvd_mul' hn hfac with h' | h'
    · exact h'
    · exact absurd h' hXe
  exact L7_tail_three hn h3 (Int.modEq_iff_dvd.mpr hA)

/-- **S0** (author p. 5, first line of §7): "Vì abc ≢ 0 (mod n), nên
a ≢ 0, b ≢ 0, c ≢ 0 (mod n)."

No cited lemma is needed: if `n ∣ a` then `n ∣ a * b * c`, so the hypothesis
transfers by multiplication of the divisor. Primality of `n` is not used
here. -/
theorem L7_step_S0 {n : ℕ} {a b c : ℤ} (h0 : ¬ (n : ℤ) ∣ a * b * c) :
    ¬ (n : ℤ) ∣ a ∧ ¬ (n : ℤ) ∣ b ∧ ¬ (n : ℤ) ∣ c := by
  refine ⟨fun h => h0 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) c),
    fun h => h0 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) c),
    fun h => h0 (dvd_mul_of_dvd_right h (a * b))⟩

/-- **S1** (author p. 5, displayed line (b)): "Từ GT2: c^n ≡ a^n + b^n (mod n²)."

The author states (b) at modulus `n²` (it is GT2 rearranged) and uses it below
at modulus `n`; both readings are recorded, the second being the one the
reductio consumes. Reducing `n²` to `n` is the `dvd_pow_self` step: `n ∣ n²`,
so a congruence mod `n²` implies the same congruence mod `n`. -/
theorem L7_step_S1 {n : ℕ} {a b c : ℤ}
    (h1 : (a ^ n + b ^ n - c ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)]) :
    (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n ^ 2 : ℤ)] ∧
      (c : ZMod n) ^ n = (a : ZMod n) ^ n + (b : ZMod n) ^ n := by
  have hd : (n ^ 2 : ℤ) ∣ a ^ n + b ^ n - c ^ n := Int.modEq_zero_iff_dvd.mp h1
  constructor
  · exact Int.modEq_iff_dvd.mpr hd
  · have hdvd : (n : ℤ) ∣ a ^ n + b ^ n - c ^ n :=
      dvd_trans (dvd_pow_self (n : ℤ) (by norm_num)) hd
    have hz : ((a ^ n + b ^ n - c ^ n : ℤ) : ZMod n) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hdvd
    have hsplit : (a : ZMod n) ^ n + (b : ZMod n) ^ n - (c : ZMod n) ^ n = 0 := by
      exact_mod_cast hz
    exact (sub_eq_zero.mp hsplit).symm

/-- **S2** (author p. 5, displayed line (c)): "Từ GT3: c^{n(n−2)} ≡ a^{n(n−2)}
+ b^{n(n−2)} (mod n)."

GT3 is already a congruence mod `n`, so this step is the same claim read as a
`ZMod n` equality — the form the reductio below consumes. -/
theorem L7_step_S2 {n : ℕ} {a b c : ℤ}
    (h2 : (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ) ≡ 0
      [ZMOD (n : ℤ)]) :
    (c : ZMod n) ^ (n * (n - 2))
      = (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2)) := by
  have hd : (n : ℤ) ∣ a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) :=
    Int.modEq_zero_iff_dvd.mp h2
  have hz : ((a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ)
      : ZMod n) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hd
  have hsplit : (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2))
      - (c : ZMod n) ^ (n * (n - 2)) = 0 := by
    exact_mod_cast hz
  exact (sub_eq_zero.mp hsplit).symm

/-- **S3 + S4** (author p. 4 bottom → p. 5, the block opening "Nếu b^n + c^n ≡ 0
(mod n)" and closing "Vậy b^n + c^n ≢ 0 (mod n)").

The chain itself is `L7_pair_reductio` at `(X, Y, Z) = (b, c, a)`; this
declaration supplies the author's (b) and (c) as `Int.ModEq` facts through the
`ZMod n` equalities S1 and S2 produce. The author's closing "Vậy …" line is
S4 and states the same `≢ 0`, so one declaration carries S3 and S4 (the
chunk's step map keeps both entries). -/
theorem L7_step_S3_S4 {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n) {a b c : ℤ}
    (hb : ¬ (n : ℤ) ∣ b)
    (h1n : (c : ZMod n) ^ n = (a : ZMod n) ^ n + (b : ZMod n) ^ n)
    (h2n : (c : ZMod n) ^ (n * (n - 2))
      = (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2))) :
    ¬ (n : ℤ) ∣ b ^ n + c ^ n := by
  have h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n : ℤ)] :=
    L7_modEq_of_zmod_eq (by push_cast; exact h1n)
  have h2 : (c ^ (n * (n - 2)) : ℤ) ≡ a ^ (n * (n - 2)) + b ^ (n * (n - 2))
      [ZMOD (n : ℤ)] :=
    L7_modEq_of_zmod_eq (by push_cast; exact h2n)
  exact L7_pair_reductio hn h3 hb h1 h2

/-- **S5** (author p. 5, first instance of "Chứng minh tương tự"): "ta cũng có
a^n + b^n ≢ 0 (mod n)."

This instance is not the b^n + c^n chain (that chain is vacuous for this pair),
but the contradiction the print's own material gives — an F3 fill-in recorded
in the chunk YAML: if `a^n + b^n ≡ 0` then (b) makes `c^n ≡ 0`, so `n ∣ c^n`
and, `n` being prime, `n ∣ c`, contradicting S0's `c ≢ 0 (mod n)`. -/
theorem L7_step_S5a {n : ℕ} (hn : Nat.Prime n) {a b c : ℤ}
    (hc : ¬ (n : ℤ) ∣ c)
    (h1n : (c : ZMod n) ^ n = (a : ZMod n) ^ n + (b : ZMod n) ^ n) :
    ¬ (n : ℤ) ∣ a ^ n + b ^ n := by
  have h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n : ℤ)] :=
    L7_modEq_of_zmod_eq (by push_cast; exact h1n)
  intro hab
  have hc0 : (c ^ n : ℤ) ≡ 0 [ZMOD (n : ℤ)] :=
    h1.trans ((Int.modEq_zero_iff_dvd).mpr hab)
  exact hc (Int.Prime.dvd_pow' hn ((Int.modEq_zero_iff_dvd).mp hc0))

/-- **S5** (author p. 5, second instance): "… c^n + a^n ≢ 0 (mod n)."

The printed "chứng minh tương tự" instance of the b^n + c^n chain: with the
assumption `c^n + a^n ≡ 0` the pair is `(X, Y) = (a, c)` and the third
variable is `Z = b`, so the author's (b) and (c) enter as `Y^n ≡ Z^n + X^n`
and `Y^e ≡ Z^e + X^e` up to `add_comm`, and the role of the cancelled factor
("vì b ≢ 0" in the printed instance) is played by `a ≢ 0 (mod n)`. -/
theorem L7_step_S5b {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n) {a b c : ℤ}
    (ha : ¬ (n : ℤ) ∣ a)
    (h1n : (c : ZMod n) ^ n = (a : ZMod n) ^ n + (b : ZMod n) ^ n)
    (h2n : (c : ZMod n) ^ (n * (n - 2))
      = (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2))) :
    ¬ (n : ℤ) ∣ c ^ n + a ^ n := by
  have h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n : ℤ)] :=
    L7_modEq_of_zmod_eq (by push_cast; exact h1n)
  have h2 : (c ^ (n * (n - 2)) : ℤ) ≡ a ^ (n * (n - 2)) + b ^ (n * (n - 2))
      [ZMOD (n : ℤ)] :=
    L7_modEq_of_zmod_eq (by push_cast; exact h2n)
  -- (b)/(c) with the pair `(X, Y) = (a, c)`, `Z = b`: the right-hand summands
  -- are commuted, nothing else changes
  have h1' : (c ^ n : ℤ) ≡ b ^ n + a ^ n [ZMOD (n : ℤ)] := by
    rw [add_comm]
    exact h1
  have h2' : (c ^ (n * (n - 2)) : ℤ) ≡ b ^ (n * (n - 2)) + a ^ (n * (n - 2))
      [ZMOD (n : ℤ)] := by
    rw [add_comm]
    exact h2
  have h := L7_pair_reductio hn h3 ha h1' h2'
  rwa [add_comm] at h

/-- **S5c** — the instance the printed "Chứng minh tương tự" line does not list
while the printed statement's product needs it: "… ta cũng có
`a^n − b^n ≢ 0 (mod n)`".

It is the printed reductio `L7_pair_reductio` re-instantiated, not a new
argument — this is the symmetry the author states in the lemma's own "Lưu ý"
paragraph ("trong hai giả thiết đồng dư (c) và (b) của Bổ đề 7 có mỗi cặp
(a; b), (c; −a), (c; −b) đối xứng nhau, nó bình đẳng và có cùng cấu trúc số học
trong vành ℤ"). Since `n` is odd, the lemma's (b) `c^n ≡ a^n + b^n` is
`a^n ≡ c^n + (−b)^n`, and its (c) is the same rearrangement at the exponent
`n(n−2)`; the reductio's conclusion `¬ n ∣ X^n + Y^n` at `(X, Y, Z) = (−b, a, c)`
is exactly `¬ n ∣ a^n − b^n`. The cancelled factor's nonzero-ness ("vì b ≢ 0"
in the printed instance) is S0's `b ≢ 0 (mod n)`. -/
theorem L7_step_S5c {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n) {a b c : ℤ}
    (hb : ¬ (n : ℤ) ∣ b)
    (h1n : (c : ZMod n) ^ n = (a : ZMod n) ^ n + (b : ZMod n) ^ n)
    (h2n : (c : ZMod n) ^ (n * (n - 2))
      = (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2))) :
    ¬ (n : ℤ) ∣ a ^ n - b ^ n := by
  have h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n : ℤ)] :=
    L7_modEq_of_zmod_eq (by push_cast; exact h1n)
  have h2 : (c ^ (n * (n - 2)) : ℤ) ≡ a ^ (n * (n - 2)) + b ^ (n * (n - 2))
      [ZMOD (n : ℤ)] :=
    L7_modEq_of_zmod_eq (by push_cast; exact h2n)
  have hodd : Odd n := hn.odd_of_ne_two (by omega)
  have hodd2 : Odd (n - 2) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k - 1, by omega⟩
  -- (b), rearranged: a^n ≡ c^n + (−b)^n
  have h1' : (a ^ n : ℤ) ≡ c ^ n + (-b) ^ n [ZMOD (n : ℤ)] := by
    refine (Int.modEq_iff_dvd).mpr ?_
    have hd := Int.modEq_iff_dvd.mp h1
    have hnb : ((-b : ℤ) ^ n) = -(b ^ n) := Odd.neg_pow hodd b
    have hid : (c ^ n + (-b) ^ n) - a ^ n = -((a ^ n + b ^ n) - c ^ n) := by
      rw [hnb]; ring
    rw [hid]
    exact dvd_neg.mpr hd
  -- (c), the same rearrangement at the exponent n(n−2) (odd, so (−b)^e = −b^e)
  have h2' : (a ^ (n * (n - 2)) : ℤ) ≡ c ^ (n * (n - 2)) + (-b) ^ (n * (n - 2))
      [ZMOD (n : ℤ)] := by
    refine (Int.modEq_iff_dvd).mpr ?_
    have hd := Int.modEq_iff_dvd.mp h2
    have hnb : ((-b : ℤ) ^ (n * (n - 2))) = -(b ^ (n * (n - 2))) :=
      Odd.neg_pow (hodd.mul hodd2) b
    have hid : (c ^ (n * (n - 2)) + (-b) ^ (n * (n - 2))) - a ^ (n * (n - 2))
        = -((a ^ (n * (n - 2)) + b ^ (n * (n - 2))) - c ^ (n * (n - 2))) := by
      rw [hnb]; ring
    rw [hid]
    exact dvd_neg.mpr hd
  have hX : ¬ (n : ℤ) ∣ (-b) := fun h => hb (dvd_neg.mp h)
  have h := L7_pair_reductio (X := -b) (Y := a) (Z := c) hn h3 hX h1' h2'
  have hid : ((-b : ℤ) ^ n + a ^ n) = a ^ n - b ^ n := by
    rw [Odd.neg_pow hodd b]; ring
  rwa [hid] at h

/-- **S6** (author p. 5, "Tóm lại, ta luôn có: (a^n − b^n)(c^n + a^n)(c^n + b^n)
≢ 0 (mod n) (đpcm)."): the product of the three facts the chain established —
S5c's `a^n − b^n ≢ 0`, S5b's `c^n + a^n ≢ 0` and S3+S4's `b^n + c^n ≢ 0` (the
printed third factor reads `c^n + b^n`, the same sum commuted) — is ≢ 0 because
`n` is prime and a prime dividing a product divides one of its factors. -/
theorem L7_step_S6 {n : ℕ} (hn : Nat.Prime n) {a b c : ℤ}
    (hd : ¬ (n : ℤ) ∣ a ^ n - b ^ n)
    (hbc : ¬ (n : ℤ) ∣ b ^ n + c ^ n)
    (hca : ¬ (n : ℤ) ∣ c ^ n + a ^ n) :
    ¬ (n : ℤ) ∣ (a ^ n - b ^ n) * (c ^ n + a ^ n) * (c ^ n + b ^ n) := by
  intro h
  rcases Int.Prime.dvd_mul' hn h with h' | h'
  · rcases Int.Prime.dvd_mul' hn h' with h'' | h''
    · exact hd h''
    · exact hca h''
  · exact hbc (by simpa [add_comm] using h')

-- evidence: permitted axioms only (propext, Classical.choice, Quot.sound)
#print axioms L7.L7_step_S0
#print axioms L7.L7_step_S1
#print axioms L7.L7_step_S2
#print axioms L7.L7_step_S3_S4
#print axioms L7.L7_step_S5a
#print axioms L7.L7_step_S5b
#print axioms L7.L7_step_S5c
#print axioms L7.L7_step_S6

-- plumbing (bridges + the author's shared reductio chain and tail)
#print axioms L7.L7_modEq_of_zmod_eq
#print axioms L7.L7_tail_three
#print axioms L7.L7_pair_reductio

end L7
