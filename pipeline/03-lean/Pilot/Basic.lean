import Mathlib

/-!
# Lemma 7 fragment — non-divisibility conclusion (chunk L7-FRAG-01)

FROZEN PRE-RESTART EXHIBIT (2026-09-25). This file is the batch attempt that
was never compiled as a whole (its steps reached F2, not S1); it is kept only
as the Lean exhibit cited by author query Q-001 and is imported by nothing.
The verified lane is `03-lean/L7/Basic.lean` (S0–S5 all S1); the `sorry` below
still marks the one step the printed chain does not support.

Verbatim formalization of the AUTHOR's proof from `PROOF_of_FERMAT.pdf`
(p. 1 statement; proof section "7. Chứng minh bổ đề 7", p. 4 bottom → p. 5)
per AGENTS.md: Lean checks the author's chain; nothing is derived by us.

Author steps encoded, in the author's order:

  P.  "Vì abc ≢ 0 (mod n), nên a ≢ 0, b ≢ 0, c ≢ 0 (mod n)."
  (b) "c^n ≡ a^n + b^n (mod n²)"                     [restatement of GT2]
  (c) "c^{n(n−2)} ≡ a^{n(n−2)} + b^{n(n−2)} (mod n)" [restatement of GT3]
  *   "Nếu b^n + c^n ≡ 0 (mod n)": c^n ≡ −b^n, a^n ≡ −2b^n,
      (−b^n)^{n−2} ≡ a^{n(n−2)}+b^{n(n−2)}, a^{n(n−2)}+2b^{n(n−2)} ≡ 0,
      (−2b^n)^{n−2}+2b^{n(n−2)} ≡ 0, −2^{n−2}+2 ≡ 0,
      −(2^{n−1}−1)+3 ≡ 0 (Fermat), 3 ≡ 0, n = 3, vô lý.
  ✓   "Vậy b^n + c^n ≢ 0 (mod n)."
  *   "Chứng minh tương tự": a^n + b^n ≢ (mod n), c^n + a^n ≢ 0 (mod n).
  *   "Tóm lại": (a^n − b^n)(c^n + a^n)(c^n + b^n) ≢ 0 (mod n) (đpcm).

FINDING (author query `pipeline/05-feedback/queries/Q-001-product-factor-sign.md`):
the printed "Chứng minh tương tự" line establishes ≢ 0 for the three pairwise
SUMS b^n+c^n, a^n+b^n, c^n+a^n, but the first factor of the STATED product is
the DIFFERENCE a^n − b^n, which no step of the printed chain excludes. The
single `sorry` below marks exactly that missing author step; every other step
of the chain compiles. Chunk status: BLOCKED on Q-001 (do not patch).

Steps (a), (d), the b^{3n}+c^{3n} chain and the "Lưu ý" symmetry paragraph
from the transcription prove the *other* conclusions of Lemma 7 (separate
chunks); they are not on this conclusion's deductive path — the author's own
contradiction says "kết hợp với (b) và (c)".
-/

namespace Pilot

theorem L7_frag_01
    {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n)
    {a b c : ℤ}
    (h0 : ¬ (n : ℤ) ∣ a * b * c)
    (h1 : (a ^ n + b ^ n - c ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h2 : (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ) ≡ 0 [ZMOD ↑n]) :
    ¬ (n : ℤ) ∣ (a ^ n - b ^ n) * (c ^ n + a ^ n) * (c ^ n + b ^ n) := by
  -- Field instance for ZMod n (n prime) + Fact for the FLT lemma.
  haveI := Fact.mk hn

  -- [plumbing, not an author step: n > 3 prime ⇒ 2 ≢ 0 (mod n)]
  have h2nz : (2 : ZMod n) ≠ 0 := by
    intro h
    have hd : (n : ℤ) ∣ 2 :=
      ZMod.intCast_zmod_eq_zero_iff_dvd.mp (by exact_mod_cast h)
    have := Int.le_of_dvd (by omega) hd
    omega

  -- Author's shared tail: "… ⇒ 3 ≡ 0 (mod n) ⇒ n = 3, vô lý."
  -- Input is the cancellation line "−2^{n−2} + 2 ≡ 0 (mod n)" (= 2^{n−2} = 2).
  have h_tail : (2 : ZMod n) ^ (n - 2) = 2 → False := by
    intro h22
    -- "⇒ −(2^{n−1} − 1) + 3 ≡ 0 (mod n)"
    have hA : -((2 : ZMod n) ^ (n - 1) - 1) + 3 = 0 := by
      have hp : (2 : ZMod n) ^ (n - 1) = 4 := by
        rw [show n - 1 = (n - 2) + 1 from by omega, pow_succ, h22]
        ring
      rw [hp]
      ring
    -- "(vì 2^{n−1} − 1 ≡ 0 (mod n), định lý nhỏ Fermat)"
    have hflt : (2 : ZMod n) ^ (n - 1) - 1 = 0 := by
      rw [ZMod.pow_card_sub_one_eq_one h2nz]
      ring
    -- "⇒ 3 ≡ 0 (mod n)"
    have h30 : (3 : ZMod n) = 0 := by
      rw [hflt] at hA
      simpa using hA
    -- "⇒ n = 3, vô lý."
    have hd : (n : ℤ) ∣ 3 :=
      ZMod.intCast_zmod_eq_zero_iff_dvd.mp (by exact_mod_cast h30)
    have := Int.le_of_dvd (by omega) hd
    omega

  -- ===== P. "Vì abc ≢ 0 (mod n), nên a ≢ 0, b ≢ 0, c ≢ 0 (mod n)" =====
  have dvd_of (x : ℤ) (hx : (x : ZMod n) = 0) : (n : ℤ) ∣ x :=
    ZMod.intCast_zmod_eq_zero_iff_dvd.mp (by exact hx)
  have ha0 : (a : ZMod n) ≠ 0 := fun h => h0 (by
    rw [mul_assoc]
    exact (dvd_of a h).mul_right (b * c))
  have hb0 : (b : ZMod n) ≠ 0 := fun h => h0 (by
    exact ((dvd_of b h).mul_left a).mul_right c)
  have hc0 : (c : ZMod n) ≠ 0 := fun h => h0 (by
    exact (dvd_of c h).mul_left (a * b))

  -- ===== (b): "c^n ≡ a^n + b^n (mod n²)" — restatement of GT2 (used mod n) =====
  have h1n : (a : ZMod n) ^ n + (b : ZMod n) ^ n = (c : ZMod n) ^ n := by
    -- GT2 reduces mod n² → mod n since n ∣ n²
    have h1n_mod : (a ^ n + b ^ n - c ^ n : ℤ) ≡ 0 [ZMOD ↑n] :=
      Int.ModEq.dvd (dvd_pow_self (n : ℤ) (by omega)) h1
    have hz : ((a ^ n + b ^ n - c ^ n : ℤ) : ZMod n) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa using Int.modEq_zero_iff_dvd.mp h1n_mod
    have hsplit : (a : ZMod n) ^ n + (b : ZMod n) ^ n - (c : ZMod n) ^ n = 0 := by
      exact_mod_cast hz
    rwa [sub_eq_zero] at hsplit

  -- ===== (c): "c^{n(n−2)} ≡ a^{n(n−2)} + b^{n(n−2)} (mod n)" — restatement of GT3 =====
  have h2n : (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2))
      = (c : ZMod n) ^ (n * (n - 2)) := by
    have hz : ((a ^ (n * (n - 2)) + b ^ (n * (n - 2))
        - c ^ (n * (n - 2)) : ℤ) : ZMod n) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa using Int.modEq_zero_iff_dvd.mp h2
    have hsplit : (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2))
        - (c : ZMod n) ^ (n * (n - 2)) = 0 := by
      exact_mod_cast hz
    rwa [sub_eq_zero] at hsplit

  -- [plumbing: n prime > 3 ⇒ n odd ⇒ n − 2 odd, used for "(vì n lẻ)" steps]
  have hne2 : n ≠ 2 := fun h => by omega
  have hodd : Odd n := (Nat.Prime.eq_two_or_odd hn).resolve_left hne2
  have hodd2 : Odd (n - 2) := by
    obtain ⟨k, hk⟩ := hodd
    use k - 1
    omega

  -- ===== "*": "Nếu b^n + c^n ≡ 0 (mod n)" ⇒ vô lý =====
  have h_bncn : (b : ZMod n) ^ n + (c : ZMod n) ^ n ≠ 0 := by
    intro hbc
    -- "thì c^n ≡ −b^n (mod n)"
    have hcz : (c : ZMod n) ^ n = -(b : ZMod n) ^ n :=
      add_eq_zero_iff_eq_neg.mp (by rwa [add_comm])
    -- "kết hợp với (b)": a^n ≡ c^n − b^n ≡ −2b^n (mod n)"
    have han : (a : ZMod n) ^ n = -2 * (b : ZMod n) ^ n := by
      have hstep : (a : ZMod n) ^ n = (c : ZMod n) ^ n - (b : ZMod n) ^ n := by
        rw [← h1n]
        ring
      rw [hcz] at hstep
      rw [hstep]
      ring
    -- "và (c)": "(−b^n)^{n−2} ≡ a^{n(n−2)} + b^{n(n−2)} (mod n)"
    have hcn : (-(b : ZMod n) ^ n) ^ (n - 2)
        = (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2)) := by
      rw [← hcz, ← pow_mul, h2n]
    -- "(vì n lẻ)": (−b^n)^{n−2} = −b^{n(n−2)}
    have hneg : (-(b : ZMod n) ^ n) ^ (n - 2)
        = -((b : ZMod n) ^ (n * (n - 2))) := by
      rw [Odd.neg_pow hodd2, pow_mul]
    have halleq : (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2))
        = -((b : ZMod n) ^ (n * (n - 2))) := hcn.symm.trans hneg
    -- "⇒ a^{n(n−2)} + 2b^{n(n−2)} ≡ 0 (mod n)"
    have hstep1 : (a : ZMod n) ^ (n * (n - 2))
        + 2 * (b : ZMod n) ^ (n * (n - 2)) = 0 := by
      calc (a : ZMod n) ^ (n * (n - 2)) + 2 * (b : ZMod n) ^ (n * (n - 2))
          = (a : ZMod n) ^ (n * (n - 2)) + (b : ZMod n) ^ (n * (n - 2))
              + (b : ZMod n) ^ (n * (n - 2)) := by ring
        _ = -((b : ZMod n) ^ (n * (n - 2))) + (b : ZMod n) ^ (n * (n - 2)) := by
              rw [halleq]
        _ = 0 := by ring
    -- "a^{n(n−2)} = (a^n)^{n−2} = (−2b^n)^{n−2}"
    have hpow_sub : (a : ZMod n) ^ (n * (n - 2))
        = (-2 * (b : ZMod n) ^ n) ^ (n - 2) := by
      rw [pow_mul, han]
    -- "⇒ (−2b^n)^{n−2} + 2b^{n(n−2)} ≡ 0 (mod n)"
    have hstep2 : (-2 * (b : ZMod n) ^ n) ^ (n - 2)
        + 2 * (b : ZMod n) ^ (n * (n - 2)) = 0 := by
      rw [← hpow_sub]
      exact hstep1
    -- "⇒ −2^{n−2} b^{n(n−2)} + 2b^{n(n−2)} ≡ 0 (mod n)"
    have hstep3 : -((2 : ZMod n) ^ (n - 2)) * (b : ZMod n) ^ (n * (n - 2))
        + 2 * (b : ZMod n) ^ (n * (n - 2)) = 0 := by
      rw [← hpow]
      exact hstep2
    -- "⇒ −2^{n−2} + 2 ≡ 0 (mod n) (vì b ≢ 0)"
    have h22 : (2 : ZMod n) ^ (n - 2) = 2 := by
      have hbe : (b : ZMod n) ^ (n * (n - 2)) ≠ 0 := pow_ne_zero _ hb0
      have hmul : (-((2 : ZMod n) ^ (n - 2)) + 2)
          * (b : ZMod n) ^ (n * (n - 2)) = 0 := by
        have h := hstep3
        rwa [← add_mul] at h
      cases mul_eq_zero.mp hmul with
      | inr h => exact absurd h hbe
      | inl h => exact neg_inj.mp (add_eq_zero_iff_eq_neg.mp h)
    -- "⇒ −(2^{n−1} − 1) + 3 ≡ 0 ⇒ 3 ≡ 0 ⇒ n = 3, vô lý."
    exact h_tail h22

  -- missing evaluation of (−2b^n)^{n−2} referenced by hstep3
  have hpow : (-2 * (b : ZMod n) ^ n) ^ (n - 2)
      = -((2 : ZMod n) ^ (n - 2)) * (b : ZMod n) ^ (n * (n - 2)) := by
    rw [mul_pow, Odd.neg_pow hodd2, pow_mul]

  -- ===== "Chứng minh tương tự ta cũng có a^n + b^n ≢ (mod n)" =====
  have h_anbn : (a : ZMod n) ^ n + (b : ZMod n) ^ n ≠ 0 := by
    intro hab
    -- "(b)": c^n ≡ a^n + b^n ≡ 0 (mod n), vô lý vì c ≢ 0 (mod n)
    have hcz : (c : ZMod n) ^ n = 0 := by
      rw [← h1n]
      exact hab
    exact hc0 (pow_eq_zero hcz)

  -- ===== "Chứng minh tương tự … c^n + a^n ≢ 0 (mod n)" =====
  have h_cnan : (c : ZMod n) ^ n + (a : ZMod n) ^ n ≠ 0 := by
    intro hca
    -- "thì c^n ≡ −a^n (mod n)"
    have hcz : (c : ZMod n) ^ n = -(a : ZMod n) ^ n :=
      add_eq_zero_iff_eq_neg.mp hca
    -- "(b)": b^n ≡ c^n − a^n ≡ −2a^n (mod n)"
    have hbn : (b : ZMod n) ^ n = -2 * (a : ZMod n) ^ n := by
      have hstep : (b : ZMod n) ^ n = (c : ZMod n) ^ n - (a : ZMod n) ^ n := by
        rw [← h1n]
        ring
      rw [hcz] at hstep
      rw [hstep]
      ring
    -- "(vì n lẻ)": c^{n(n−2)} = −a^{n(n−2)}"
    have hce : (c : ZMod n) ^ (n * (n - 2))
        = -((a : ZMod n) ^ (n * (n - 2))) := by
      rw [pow_mul, hcz, Odd.neg_pow hodd2]
    -- b^{n(n−2)} = (−2a^n)^{n−2} = −2^{n−2} a^{n(n−2)}"
    have hbe : (b : ZMod n) ^ (n * (n - 2))
        = -((2 : ZMod n) ^ (n - 2)) * (a : ZMod n) ^ (n * (n - 2)) := by
      rw [pow_mul, hbn, mul_pow, Odd.neg_pow hodd2]
    -- same template: cancellation ⇒ 2^{n−2} ≡ 2 ⇒ n = 3, vô lý
    have hkey : (2 - (2 : ZMod n) ^ (n - 2))
        * (a : ZMod n) ^ (n * (n - 2)) = 0 := by
      have hraw := h2n
      rw [hbe, hce] at hraw
      have hbridge : (2 - (2 : ZMod n) ^ (n - 2))
          * (a : ZMod n) ^ (n * (n - 2))
          = (a : ZMod n) ^ (n * (n - 2))
              + (-((2 : ZMod n) ^ (n - 2)) * (a : ZMod n) ^ (n * (n - 2)))
              - (-(a : ZMod n) ^ (n * (n - 2))) := by
        ring
      rw [hbridge, ← hraw]
      ring
    have h22 : (2 : ZMod n) ^ (n - 2) = 2 := by
      cases mul_eq_zero.mp hkey with
      | inl h => exact (sub_eq_zero.mp h).symm
      | inr h => exact absurd h (pow_ne_zero _ ha0)
    exact h_tail h22

  -- ===== "Tóm lại, ta luôn có: (a^n − b^n)(c^n + a^n)(c^n + b^n) ≢ 0 (mod n)" =====
  have h_factor1 : (a : ZMod n) ^ n - (b : ZMod n) ^ n ≠ 0 := by
    intro hf
    rw [sub_eq_zero] at hf
    -- === FINDING: author query Q-001 (pipeline/05-feedback/queries/) ===
    -- The printed proof's "Chứng minh tương tự" line establishes ≢ 0 for
    -- a^n + b^n (with b^n + c^n, c^n + a^n), but the first factor of the
    -- STATED product is the DIFFERENCE a^n − b^n, which no step of the
    -- printed chain excludes. Chunk is BLOCKED on Q-001 — do not patch.
    sorry

  intro hprod
  have hz : (((a ^ n - b ^ n) * (c ^ n + a ^ n)
      * (c ^ n + b ^ n : ℤ)) : ZMod n) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hprod
  have hzmod : ((a : ZMod n) ^ n - (b : ZMod n) ^ n)
      * ((c : ZMod n) ^ n + (a : ZMod n) ^ n)
      * ((c : ZMod n) ^ n + (b : ZMod n) ^ n) = 0 := by
    exact_mod_cast hz
  cases mul_eq_zero.mp hzmod with
  | inl h12 =>
    cases mul_eq_zero.mp h12 with
    | inl hf => exact h_factor1 hf
    | inr hf => exact h_cnan hf
  | inr hf => exact h_bncn hf

end Pilot
