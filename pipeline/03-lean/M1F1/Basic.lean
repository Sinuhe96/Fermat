/-
Chunk `M1-FRAG-01` — the main proof, pp. 6–7 (`D. CHỨNG MINH ĐỊNH LÝ LỚN FERMAT`, §1).

The author's steps from region `P006-R1` (signed LaTeX; the Vietnamese source
text lives in `pipeline/02-chunks/chunks/M1-FRAG-01.yml`, never retyped here).
Step order follows the print: S0 (bổ đề 1), S1 (the sign symmetry), S3 (bổ đề 6),
S4 (the substitution into (3)). S2 is the author's WLOG choice and is carried as
the two hypotheses `hnu`, `hnv` of S3, exactly as the print carries it as an
assumption rather than a claim.

The `#check` block is the lane's batched name pin (M1_LANE.md §1 step 3): it
rides in the same round as the proof text, so one 250–400 s compile answers both
"does this name exist as spelled" and "does the step go through".
-/
import Mathlib
import L1.Basic
import L6.Basic

-- name pin for S0/S1/S3 (round 3; `Nat.Prime.prime_int` does not exist at this
-- pin and was removed after the round reported it)
#check @Nat.Prime.odd_of_ne_two
#check @Nat.Prime.two_le
#check @Nat.Prime.eq_two_or_odd
#check @Nat.Prime.prime
#check @Int.prime_iff_natAbs_prime
#check @Prime.dvd_mul
#check @Odd.neg_pow
#check @L1.L1_bo_de_1
#check @L6.L6_bo_de_6

namespace M1F1

/-- **S0** (author p. 6, region `P006-R1`).

The print's opening move: a prime `n > 11` and a nonzero integral solution of (1)
are reduced by bổ đề 1 to pairwise-coprime `u, v, t` with `u^n + v^n = t^n`,
which the print labels (3). This is bổ đề 1 read at the lane's hypothesis; the
only formal content added is `3 ≤ n`, which the print has as `n > 11`. -/
theorem M1F1_step_S0_reduce {n : ℕ} (hn : Nat.Prime n) (hn12 : 12 ≤ n)
    {u₀ v₀ t₀ : ℤ} (hu₀ : u₀ ≠ 0) (hv₀ : v₀ ≠ 0) (ht₀ : t₀ ≠ 0)
    (hsol : u₀ ^ n + v₀ ^ n = t₀ ^ n) :
    ∃ u v t : ℤ, u ≠ 0 ∧ v ≠ 0 ∧ t ≠ 0 ∧ u ^ n + v ^ n = t ^ n ∧
      Int.gcd u v = 1 ∧ Int.gcd u t = 1 ∧ Int.gcd v t = 1 := by
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    omega
  exact L1.L1_bo_de_1 hn3 hu₀ hv₀ ht₀ hsol

/-- **S1** (author p. 6, region `P006-R1`).

"Vì `n` lẻ ... `u^n + v^n = t^n` ⟺ `v^n + u^n = t^n` ⟺ `(-t)^n + v^n = (-u)^n`
⟺ `u^n + (-t)^n = (-v)^n`; do đó, tính chất số học và vai trò của `u, v, t` là
như nhau."

The four printed forms are equivalent exactly when `n` is odd: the sign step is
`Odd.neg_pow`, `(-x)^n = -(x^n)`. This is the licence the print invokes for its
WLOG choice (S2); it claims nothing beyond these three biconditionals. -/
theorem M1F1_step_S1_symmetry {n : ℕ} (hodd : Odd n) (u v t : ℤ) :
    (u ^ n + v ^ n = t ^ n ↔ v ^ n + u ^ n = t ^ n) ∧
      (u ^ n + v ^ n = t ^ n ↔ (-t) ^ n + v ^ n = (-u) ^ n) ∧
      (u ^ n + v ^ n = t ^ n ↔ u ^ n + (-t) ^ n = (-v) ^ n) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> intro hg <;> linarith
  · constructor
    · intro hg
      rw [hodd.neg_pow, hodd.neg_pow]
      linarith
    · intro hg
      rw [hodd.neg_pow, hodd.neg_pow] at hg
      linarith
  · constructor
    · intro hg
      rw [hodd.neg_pow, hodd.neg_pow]
      linarith
    · intro hg
      rw [hodd.neg_pow, hodd.neg_pow] at hg
      linarith

/-- **S3** (author p. 6, region `P006-R1`).

"không mất tính tổng quát ta giả sử `u ∤ n`, `v ∤ n`, áp dụng bổ đề 6, ta có:
`v = a^n + n^s abck`, `u = b^n + n^s abck`, `t = h - n^s abck`,
`a^n + b^n = h - 2n^s abck`".

`h` is carried as the printed pair of cases (`t ∤ n → h = c^n`;
`n | t → h = n^{ns-1}c^n`), which is how the DONE entry point returns it; the
print does not branch on it here. The hypotheses `hnu`, `hnv` are S2's WLOG
assumption (see the chunk record): the print asserts `n ∤ u`, `n ∤ v` and does
not derive them, and this file does not strengthen that. `n` prime plus those two
non-divisibilities give `n ∤ u*v`, which is what bổ đề 6 needs. -/
theorem M1F1_step_S3_bo_de_6 {n : ℕ} (hn : Nat.Prime n) (hn12 : 12 ≤ n)
    {u v t : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (ht : t ≠ 0)
    (hsol : u ^ n + v ^ n = t ^ n)
    (huv : Int.gcd u v = 1) (hut : Int.gcd u t = 1) (hvt : Int.gcd v t = 1)
    (hnu : ¬ (n : ℤ) ∣ u) (hnv : ¬ (n : ℤ) ∣ v) :
    ∃ a b c k h : ℤ, ∃ s : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ k ≠ 0 ∧
      Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd c b = 1 ∧
      Int.gcd a k = 1 ∧ Int.gcd b k = 1 ∧ Int.gcd c k = 1 ∧
      ¬ (n : ℤ) ∣ a ∧ ¬ (n : ℤ) ∣ b ∧ ¬ (n : ℤ) ∣ c ∧ ¬ (n : ℤ) ∣ k ∧
      2 ≤ s ∧
      v = a ^ n + (n : ℤ) ^ s * (a * b * c * k) ∧
      u = b ^ n + (n : ℤ) ^ s * (a * b * c * k) ∧
      t = h - (n : ℤ) ^ s * (a * b * c * k) ∧
      a ^ n + b ^ n = h - 2 * ((n : ℤ) ^ s * (a * b * c * k)) ∧
      (¬ (n : ℤ) ∣ t → h = c ^ n) ∧
      ((n : ℤ) ∣ t → h = (n : ℤ) ^ (n * s - 1) * c ^ n) := by
  have hodd : Odd n := hn.odd_of_ne_two (by omega)
  have huvn : ¬ (n : ℤ) ∣ u * v := by
    intro h
    have hprime : Prime (n : ℤ) :=
      Int.prime_iff_natAbs_prime.mpr (by simpa using hn)
    rcases hprime.dvd_mul.mp h with h' | h'
    · exact hnu h'
    · exact hnv h'
  exact L6.L6_bo_de_6 hn hodd hu hv ht hsol huv hut hvt huvn

/-- **S4** (author p. 6, region `P006-R1`, last display).

"Ta có: (3) ⇒ `(a^n + n^s abck)^n + (b^n + n^s abck)^n = (h - n^s abck)^n`" — the
substitution of S3's four identities into (3), nothing more. The expansion of
that identity into the printed alternating sum (and the truncations (7)–(10))
are the following leaves, not this step. -/
theorem M1F1_step_S4_substitute {n s : ℕ} {a b c k h u v t : ℤ}
    (hv : v = a ^ n + (n : ℤ) ^ s * (a * b * c * k))
    (hu : u = b ^ n + (n : ℤ) ^ s * (a * b * c * k))
    (ht : t = h - (n : ℤ) ^ s * (a * b * c * k))
    (hsol : u ^ n + v ^ n = t ^ n) :
    (a ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
        + (b ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n
      = (h - (n : ℤ) ^ s * (a * b * c * k)) ^ n := by
  rw [← hv, ← hu, ← ht]
  linarith

end M1F1

-- DONE-flip evidence: the permitted axioms only (propext, Classical.choice,
-- Quot.sound); anything else — and any `sorryAx` — blocks the flip.
#print axioms M1F1.M1F1_step_S0_reduce
#print axioms M1F1.M1F1_step_S1_symmetry
#print axioms M1F1.M1F1_step_S3_bo_de_6
#print axioms M1F1.M1F1_step_S4_substitute
