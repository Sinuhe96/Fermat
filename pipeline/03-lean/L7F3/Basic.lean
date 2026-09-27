import Mathlib
import L5.Basic
import L7F2.Basic

/-!
# Lemma 7 (bổ đề 7) — b^{3n}+c^{3n} ≡ 0 (mod n²) and its symmetric instances
(chunk L7-FRAG-03)

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. 2 top (the conclusion list) and p. 30 R2, forms (19) and (20);
  * proof: p. 5 §7, immediately after the displayed (d), plus the "Lưu ý"
    symmetry paragraph.

The literal transcription and the ordered step map live in
`pipeline/02-chunks/chunks/L7-FRAG-03.yml`. One named declaration per author
step (English paraphrase):

  S5     "⇒ a^n b^n ≡ (a^n+b^n)² (mod n) ⇒ … ⇒ b^{2n}+a^nc^n ≡ 0 (mod n)"
                                                              -> L7F3_step_S5
  S6     "⇒ b^{3n}+c^n(a^nb^n) ≡ 0 ⇒ b^{3n}+c^{3n} ≡ 0 (mod n)"
                                                              -> L7F3_step_S6
  S7     "⇒ (b^{3n})^n+(c^{3n})^n ≡ 0 (mod n²) (áp dụng bổ đề 5c)"
                                                              -> L7F3_step_S7
  S8+S9  the rewrite (b^{3n})^n = (b³)^{n(n−1)}·b^{3n} + bổ đề 5d at b³, c³
                                                              -> L7F3_step_S8_S9
  S9     the printed chain S5–S9 in one piece at the printed pair (a,b) — the
         conclusion (19) `b^{3n}+c^{3n} ≡ 0 (mod n²)`          -> L7F3_chain_ab
  S10    the "Lưu ý" symmetry instance with (a;b) swapped ⇒
         (20)'s `a^{3n}+c^{3n} ≡ 0 (mod n²)`                  -> L7F3_step_S10
  S11    with c^{3n} ≡ −b^{3n}: `a^{3n}−b^{3n} ≡ 0 (mod n²)`   -> L7F3_step_S11

## Encoding decisions

* The printed chain is written once for the pair `(a, b)`; the "Lưu ý"
  paragraph states that (b) and (c) are symmetric under `(a; b)` (and
  `(c; −a)`, `(c; −b)`), and re-instantiates it. S5–S8_S9 are therefore stated
  for an abstract pair `(X, Y)`, and the two instances are the printed
  `(X, Y) = (a, b)` (`L7F3_chain_ab`, giving (19)) and the swap
  `(X, Y) = (b, a)` (`L7F3_step_S10`). The abstraction is the print's own
  claim of analogy — the same device as `L7_pair_reductio` in chunk
  L7-FRAG-01, not a new proof route.
* S7's premise is an F3 fill-in (recorded in the chunk YAML): bổ đề 5c needs
  `n ∣ (b^{3n})^n + (c^{3n})^n`, which the print leaves implicit (it raises
  `n ∣ b^{3n}+c^{3n}` to the n-th power, `n` being odd). The premise is derived
  inside `L7F3_step_S7` from the printed S6 output.
* `L7F3_five_c` is bổ đề 5c's statement *without* bổ đề 5's coprimality
  hypothesis — the print itself notes "(không cần giả thiết (u,v) = 1)" — and
  is assembled from bổ đề 5's exposed branch theorems `S12`/`S15`/`S16`.
  `L7F3_five_d_cube` is bổ đề 5d at a cube (`x³ ⋮̸ n`), the form the print uses
  at `b³` and `c³`.
-/

namespace L7

/-- bổ đề 5c without bổ đề 5's coprimality hypothesis (the author's own
"(không cần giả thiết `(u,v) = 1`)"): assembled from bổ đề 5's exposed branches
— `uv ⋮ n` (S12), and `uv ⋮̸ n` ⇒ `(u+v) ⋮ n` (S15) ⇒ `n² ∣ u^n+v^n` (S16). -/
theorem L7F3_five_c {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {u v : ℤ}
    (hsol : (n : ℤ) ∣ u ^ n + v ^ n) : (n : ℤ) ^ 2 ∣ u ^ n + v ^ n := by
  by_cases huv : (n : ℤ) ∣ u * v
  · exact L5.L5_step_S12 hn huv hsol
  · exact L5.L5_step_S16 hodd (L5.L5_step_S15 hn hodd huv hsol)

/-- bổ đề 5d at a cube: `(x³)^{n(n−1)} ≡ 1 (mod n²)` for `x ⋮̸ n` — the form the
printed chain applies at `b³` and `c³` (S9), from `b ⋮̸ n`, `c ⋮̸ n`. -/
theorem L7F3_five_d_cube {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {x : ℤ}
    (hx : ¬ (n : ℤ) ∣ x) : ((x ^ 3) ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)] := by
  have hx3 : ¬ (n : ℤ) ∣ x ^ 3 := fun h => hx (Int.Prime.dvd_pow' hn (k := 3) h)
  obtain ⟨m, hm⟩ := L5.L5_step_S17 hn hodd hx3
  simpa using L5.L5_step_S18 hm

/-- **S5** (author p. 5 §7): "⇒ a^n b^n ≡ (a^n+b^n)² (mod n) ⇒
b^{2n}+a^nb^n+a^{2n} ≡ 0 (mod n) ⇒ b^{2n}+a^n(a^n+b^n) ≡ 0 (mod n) ⇒
b^{2n}+a^nc^n ≡ 0 (mod n) (vì a^n+b^n ≡ c^n (mod n²))".

Stated for the abstract pair `(X, Y)` (printed instance `X = a, Y = b`; the
swap `(X, Y) = (b, a)` is the print's "Lưu ý" symmetry, used by S10). -/
theorem L7F3_step_S5 {n : ℕ} {X Y c : ℤ}
    (h1 : (c ^ n : ℤ) ≡ X ^ n + Y ^ n [ZMOD (n : ℤ)])
    (h2 : (X ^ n * Y ^ n : ℤ) ≡ c ^ (2 * n) [ZMOD (n : ℤ)]) :
    (Y ^ (2 * n) + X ^ n * c ^ n : ℤ) ≡ 0 [ZMOD (n : ℤ)] := by
  -- "a^n b^n ≡ (a^n+b^n)² (mod n)"
  have h2' : (X ^ n * Y ^ n : ℤ) ≡ (c ^ n) ^ 2 [ZMOD (n : ℤ)] := by
    have hcc : (c ^ (2 * n) : ℤ) = (c ^ n) ^ 2 := by rw [Nat.mul_comm 2 n, pow_mul]
    rwa [hcc] at h2
  have hsq : (X ^ n * Y ^ n : ℤ) ≡ (X ^ n + Y ^ n) ^ 2 [ZMOD (n : ℤ)] :=
    h2'.trans (h1.pow 2)
  -- "b^{2n}+a^n(a^n+b^n) ≡ 0 (mod n)"
  have hY2 : Y ^ (2 * n) = (Y ^ n) ^ 2 := by rw [Nat.mul_comm 2 n, pow_mul]
  have hstep : (Y ^ (2 * n) + X ^ n * (X ^ n + Y ^ n) : ℤ) ≡ 0 [ZMOD (n : ℤ)] := by
    have hkey : (Y ^ (2 * n) + X ^ n * (X ^ n + Y ^ n) : ℤ)
        = (X ^ n + Y ^ n) ^ 2 - X ^ n * Y ^ n := by
      rw [hY2]; ring
    rw [hkey]
    simpa using hsq.symm.sub (Int.ModEq.refl (X ^ n * Y ^ n))
  -- "b^{2n}+a^nc^n ≡ 0 (mod n)"
  have hmul : (X ^ n * (X ^ n + Y ^ n) : ℤ) ≡ X ^ n * c ^ n [ZMOD (n : ℤ)] :=
    h1.symm.mul_left (X ^ n)
  exact (hmul.symm.add_left (Y ^ (2 * n))).trans hstep

/-- **S6** (author p. 5 §7): "⇒ b^{3n}+c^n(a^nb^n) ≡ 0 (mod n) ⇒ b^{3n}+c^{3n}
≡ 0 (mod n) (vì a^nb^n ≡ c^{2n} (mod n))". -/
theorem L7F3_step_S6 {n : ℕ} {X Y c : ℤ}
    (h5 : (Y ^ (2 * n) + X ^ n * c ^ n : ℤ) ≡ 0 [ZMOD (n : ℤ)])
    (h2 : (X ^ n * Y ^ n : ℤ) ≡ c ^ (2 * n) [ZMOD (n : ℤ)]) :
    (Y ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n : ℤ)] := by
  -- multiply S5 by Y^n: "b^{3n}+c^n(a^nb^n) ≡ 0"
  have hmul : (Y ^ n * (Y ^ (2 * n) + X ^ n * c ^ n) : ℤ) ≡ 0 [ZMOD (n : ℤ)] := by
    simpa using h5.mul_left (Y ^ n)
  have hL : (Y ^ n * (Y ^ (2 * n) + X ^ n * c ^ n) : ℤ)
      = Y ^ (3 * n) + X ^ n * Y ^ n * c ^ n := by
    rw [mul_add, ← pow_add, show n + 2 * n = 3 * n from by ring]
    ring
  have hL' : (Y ^ (3 * n) + X ^ n * Y ^ n * c ^ n : ℤ) ≡ 0 [ZMOD (n : ℤ)] := by
    rwa [hL] at hmul
  -- "vì a^nb^n ≡ c^{2n} (mod n)"
  have h2c : (X ^ n * Y ^ n * c ^ n : ℤ) ≡ c ^ (3 * n) [ZMOD (n : ℤ)] := by
    have h := h2.mul_right (c ^ n)
    have hc : (c ^ (2 * n) * c ^ n : ℤ) = c ^ (3 * n) := by
      rw [← pow_add, show 2 * n + n = 3 * n from by ring]
    rwa [hc] at h
  exact (h2c.symm.add_left (Y ^ (3 * n))).trans hL'

/-- **S7** (author p. 5 §7): "⇒ (b^{3n})^n + (c^{3n})^n ≡ 0 (mod n²) (áp dụng
bổ đề 5c)".

F3 fill-in (recorded in the chunk YAML): bổ đề 5c needs the premise
`n ∣ (Y^{3n})^n + (c^{3n})^n`, which the print leaves implicit — it raises
`n ∣ Y^{3n}+c^{3n}` (the line above) to the n-th power, `n` being odd. The
premise is derived here; 5c in its coprimality-free form (`L7F3_five_c`) then
supplies the divisibility by `n²`. -/
theorem L7F3_step_S7 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {Y c : ℤ}
    (h6 : (Y ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n : ℤ)]) :
    (n ^ 2 : ℤ) ∣ (Y ^ (3 * n)) ^ n + (c ^ (3 * n)) ^ n := by
  have hX : (Y ^ (3 * n) : ℤ) ≡ (-(c ^ (3 * n))) [ZMOD (n : ℤ)] := by
    simpa using h6.add_right (-(c ^ (3 * n)))
  have hprem : (n : ℤ) ∣ (Y ^ (3 * n)) ^ n + (c ^ (3 * n)) ^ n := by
    have hp := hX.pow n
    have hneg : ((-(c ^ (3 * n)) : ℤ)) ^ n = -((c ^ (3 * n)) ^ n) := Odd.neg_pow hodd _
    rw [hneg] at hp
    have h1 := hp.add_right ((c ^ (3 * n)) ^ n)
    have hid : (-((c ^ (3 * n)) ^ n) + (c ^ (3 * n)) ^ n : ℤ) = 0 := by ring
    rw [hid] at h1
    exact Int.modEq_zero_iff_dvd.mp h1
  simpa using L7F3_five_c hn hodd hprem

/-- **S8 + S9** (author p. 5 §7): the rewrite `(b^{3n})^n = (b³)^{n(n−1)}·b^{3n}`
followed by "áp dụng bổ đề 5d: (b³)^{n(n−1)} ≡ (c³)^{n(n−1)} ≡ 1 (mod n²)",
giving `b^{3n}+c^{3n} ≡ 0 (mod n²)`.

The two 5d facts enter as hypotheses (the print derives them from `b ⋮̸ n`,
`c ⋮̸ n` via `L7F3_five_d_cube`, which the instances below apply). -/
theorem L7F3_step_S8_S9 {n : ℕ} {Y c : ℤ}
    (h7 : (n ^ 2 : ℤ) ∣ (Y ^ (3 * n)) ^ n + (c ^ (3 * n)) ^ n)
    (hY3 : ((Y ^ 3) ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)])
    (hc3 : ((c ^ 3) ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)]) :
    (Y ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  -- the printed rewrite: (x^{3n})^n = (x³)^{n(n−1)} · x^{3n}
  have hexp : n * (n - 1) + n = n * n := by
    cases n with
    | zero => simp
    | succ k => rw [show k + 1 - 1 = k from by omega, Nat.mul_succ]
  have hrew : ∀ x : ℤ,
      ((x ^ 3) ^ (n * (n - 1)) * x ^ (3 * n) : ℤ) = (x ^ (3 * n)) ^ n := by
    intro x
    rw [pow_mul x 3 n, ← pow_add, hexp, pow_mul (x ^ 3) n n]
  -- 5d collapses the product to x^{3n}
  have hcube : ∀ x : ℤ, ((x ^ 3) ^ (n * (n - 1)) : ℤ) ≡ 1 [ZMOD (n ^ 2 : ℤ)] →
      (x ^ (3 * n)) ^ n ≡ x ^ (3 * n) [ZMOD (n ^ 2 : ℤ)] := by
    intro x hx
    have hup : ((x ^ 3) ^ (n * (n - 1)) * x ^ (3 * n) : ℤ)
        ≡ x ^ (3 * n) [ZMOD (n ^ 2 : ℤ)] := by
      simpa using hx.mul_right (x ^ (3 * n))
    rwa [hrew x] at hup
  have hsum : ((Y ^ (3 * n)) ^ n + (c ^ (3 * n)) ^ n : ℤ)
      ≡ Y ^ (3 * n) + c ^ (3 * n) [ZMOD (n ^ 2 : ℤ)] :=
    (hcube Y hY3).add (hcube c hc3)
  exact hsum.symm.trans (Int.modEq_zero_iff_dvd.mpr h7)

/-- **S9** (author p. 5 §7, the printed chain in one piece): S5 → S6 → S7 →
S8+S9 at the printed pair `(X, Y) = (a, b)`, the two 5d facts coming from
`b ⋮̸ n` and `c ⋮̸ n`:

  "⇒ b^{3n}+c^{3n} ≡ 0 (mod n²)"

— the main proof's (19) (with its companion `c^{3n} ≡ −b^{3n}`). -/
theorem L7F3_chain_ab {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {a b c : ℤ}
    (hb : ¬ (n : ℤ) ∣ b) (hc : ¬ (n : ℤ) ∣ c)
    (h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n : ℤ)])
    (h2 : (a ^ n * b ^ n : ℤ) ≡ c ^ (2 * n) [ZMOD (n : ℤ)]) :
    (b ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] :=
  L7F3_step_S8_S9 (n := n)
    (L7F3_step_S7 hn hodd (L7F3_step_S6 (L7F3_step_S5 (X := a) (Y := b) h1 h2) h2))
    (L7F3_five_d_cube hn hodd hb) (L7F3_five_d_cube hn hodd hc)

/-- **S10** (author p. 5 §7, the "Lưu ý" symmetry paragraph): "Cho nên, nếu có
b^{3n}+c^{3n} ≡ 0 (mod n²) thì ta cũng có a^{3n}+c^{3n} ≡ 0 (mod n²)" — the
printed chain re-instantiated with `(a; b)` swapped, which is the author's own
statement that (b) and (c) are symmetric under that pair. -/
theorem L7F3_step_S10 {n : ℕ} (hn : Nat.Prime n) (hodd : Odd n) {a b c : ℤ}
    (ha : ¬ (n : ℤ) ∣ a) (hc : ¬ (n : ℤ) ∣ c)
    (h1 : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n : ℤ)])
    (h2 : (a ^ n * b ^ n : ℤ) ≡ c ^ (2 * n) [ZMOD (n : ℤ)]) :
    (a ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] :=
  L7F3_step_S8_S9 (n := n)
    (L7F3_step_S7 hn hodd (L7F3_step_S6 (L7F3_step_S5 (X := b) (Y := a)
        (by simpa [add_comm] using h1) (by simpa [mul_comm] using h2))
      (by simpa [mul_comm] using h2)))
    (L7F3_five_d_cube hn hodd ha) (L7F3_five_d_cube hn hodd hc)

/-- **S11** (author p. 5 §7, the "Lưu ý" paragraph): "hay a^{3n}+c^{3n} ≡
a^{3n}−b^{3n} ≡ 0 (mod n²)" — the main proof's (20), from the printed (19)
(`b^{3n}+c^{3n} ≡ 0`) and S10 (`a^{3n}+c^{3n} ≡ 0`). -/
theorem L7F3_step_S11 {n : ℕ} {a b c : ℤ}
    (h9 : (b ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h10 : (a ^ (3 * n) + c ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)]) :
    (a ^ (3 * n) - b ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have hm : (c ^ (3 * n) : ℤ) ≡ (-(b ^ (3 * n))) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using h9.add_right (-(b ^ (3 * n)))
  have hfinal : (a ^ (3 * n) + -(b ^ (3 * n)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] :=
    (h10.symm.trans (hm.add_left (a ^ (3 * n)))).symm
  simpa [sub_eq_add_neg] using hfinal

end L7
