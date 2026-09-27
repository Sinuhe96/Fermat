import Mathlib
import L7.Basic
import L7F2.Basic
import L7F3.Basic
import L7F4.Basic
import L7F5.Basic
import L7F6.Basic

/-!
# Lemma 7 (bổ đề 7) — section assembly (chunk L7-ASM)

Chains the leaf chunks' assembly theorems into the lemma's full conclusion
list, in the author's order (AGENTS.md "Section assembly": no new mathematics,
no re-proved steps):

  L7-FRAG-01  the non-divisibility product `(a^n−b^n)(c^n+a^n)(c^n+b^n) ⋮̸ n`
  L7-FRAG-02  (a) `a^{n²}+b^{n²}−c^{n²} ≡ 0 (mod n²)` and the (b), (c), (d) toolkit
  L7-FRAG-03  (19) `b^{3n}+c^{3n} ≡ 0 (mod n²)`, S10 `a^{3n}+c^{3n} ≡ 0`,
              (20) `a^{3n}−b^{3n} ≡ 0 (mod n²)`
  L7-FRAG-04  (18) `a^{2n}+b^nc^n ≡ b^{2n}+a^nc^n ≡ c^{2n}−a^nb^n ≡ 0 (mod n²)`
              and (22') `a^{n(n−2)}+b^{n(n−2)}−c^{n(n−2)} ≡ 0 (mod n²)`
  L7-FRAG-05  `n ≡ 1 (mod 6)`
  L7-FRAG-06  (21) the `a^{n(n−4)}` group and (22) `a^{n(n−3)}+b^{n(n−3)}+c^{n(n−3)} ≡ 0`

The literal statement and the conclusion list are in
`pipeline/02-chunks/chunks/L7-ASM.yml`; the numbered forms (18)–(22') are the
ones the main proof cites at p. 30 R2 and p. 31.
-/

namespace L7

/-- **Bổ đề 7** (statement p. 1 bottom → p. 2 top): for a prime `n > 3` and
integers `a, b, c` with `abc ≢ 0 (mod n)`,
`a^n+b^n−c^n ≡ 0 (mod n²)` and `a^{n(n−2)}+b^{n(n−2)}−c^{n(n−2)} ≡ 0 (mod n)`:

* `(a^n−b^n)(c^n+a^n)(c^n+b^n) ≢ 0 (mod n)` (chunk L7-FRAG-01);
* `a^{n²}+b^{n²}−c^{n²} ≡ 0 (mod n²)` — display (a) (L7-FRAG-02);
* the `a^{n(n−3)}+b^{n(n−3)}+c^{n(n−3)}` group: (19) `c^{3n}+b^{3n} ≡ 0`,
  `a^{3n}+c^{3n} ≡ 0`, (20) `a^{3n}−b^{3n} ≡ 0`, (18)
  `b^nc^n+a^{2n} ≡ c^na^n+b^{2n} ≡ b^na^n−c^{2n} ≡ 0` — all mod `n²`
  (L7-FRAG-03, L7-FRAG-04);
* `n ≡ 1 (mod 6)` (L7-FRAG-05);
* (21) `a^{n(n−4)}+c^{n(n−4)} ≡ b^{n(n−4)}+c^{n(n−4)} ≡ a^{n(n−4)}−b^{n(n−4)} ≡ 0`,
  (22) `a^{n(n−3)}+b^{n(n−3)}+c^{n(n−3)} ≡ 0` and (22')
  `a^{n(n−2)}+b^{n(n−2)}−c^{n(n−2)} ≡ 0`, all mod `n²` (L7-FRAG-06, L7-FRAG-04). -/
theorem L7_bo_de_7 {n : ℕ} (hn : Nat.Prime n) (h3 : 3 < n) {a b c : ℤ}
    (habc : ¬ (n : ℤ) ∣ a * b * c)
    (h2 : (a ^ n + b ^ n - c ^ n : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)])
    (h3c : (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ)
      ≡ 0 [ZMOD (n : ℤ)]) :
    ¬ (n : ℤ) ∣ (a ^ n - b ^ n) * (c ^ n + a ^ n) * (c ^ n + b ^ n) ∧
      (a ^ (n ^ 2) + b ^ (n ^ 2) - c ^ (n ^ 2) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (c ^ (3 * n) + b ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (a ^ (3 * n) - b ^ (3 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (b ^ n * c ^ n + a ^ (2 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (c ^ n * a ^ n + b ^ (2 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (b ^ n * a ^ n - c ^ (2 * n) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (a ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (b ^ (n * (n - 4)) + c ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (a ^ (n * (n - 4)) - b ^ (n * (n - 4)) : ℤ) ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (a ^ (n * (n - 3)) + b ^ (n * (n - 3)) + c ^ (n * (n - 3)) : ℤ)
        ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      (a ^ (n * (n - 2)) + b ^ (n * (n - 2)) - c ^ (n * (n - 2)) : ℤ)
        ≡ 0 [ZMOD (n ^ 2 : ℤ)] ∧
      n % 6 = 1 := by
  have hodd : Odd n := hn.odd_of_ne_two (by omega)
  -- S0 of §7: `abc ≢ 0 (mod n)` gives the three coordinates
  obtain ⟨ha, hb, hc⟩ := L7_step_S0 habc
  -- the (b)/(c)/(d) toolkit (L7-FRAG-02), and 5d at a, b, c
  have h5d := L7F2_step_S0 hn h3 ha hb hc
  have hbc := L7F2_step_S2 h2 h3c
  have hS3 := L7F2_step_S3 hn hbc.2 h5d.1 h5d.2.1 h5d.2.2
  have hS4 := L7F2_step_S4 hS3 hbc.1
  have hAn := hbc.1
  have hAn' : (c ^ n : ℤ) ≡ a ^ n + b ^ n [ZMOD (n : ℤ)] :=
    Int.ModEq.of_dvd (dvd_pow_self (n : ℤ) (by norm_num)) hbc.1
  -- (a)
  have hqa := L7F2_step_S1 hn h2 h5d.1 h5d.2.1 h5d.2.2
  -- the non-divisibility product (L7-FRAG-01)
  have h1z := L7_step_S1 h2
  have h2z := L7_step_S2 h3c
  have hprod := L7_step_S6 hn (L7_step_S5c hn h3 hb h1z.2 h2z)
    (L7_step_S3_S4 hn h3 hb h1z.2 h2z) (L7_step_S5b hn h3 ha h1z.2 h2z)
  -- (19), S10, (20) — the b^{3n}+c^{3n} chain and its symmetric instances
  have h19 := L7F3_chain_ab hn hodd hb hc hAn' hS4
  have h19neg : (c ^ (3 * n) : ℤ) ≡ (-(b ^ (3 * n))) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using h19.add_right (-(b ^ (3 * n)))
  have h10 := L7F3_step_S10 hn hodd ha hc hAn' hS4
  have h20 := L7F3_step_S11 h19 h10
  have h20c : (a ^ (3 * n) : ℤ) ≡ b ^ (3 * n) [ZMOD (n ^ 2 : ℤ)] := by
    simpa using h20.add_right (b ^ (3 * n))
  -- (18) and (22')
  have hS12 := L7F4_step_S12 hn h19 hAn (L7_step_S3_S4 hn h3 hb h1z.2 h2z)
  have hS13 := L7F4_step_S13 hn h10 h20 hAn
    (by simpa [add_comm] using L7_step_S5b hn h3 ha h1z.2 h2z)
    (L7_step_S5c hn h3 hb h1z.2 h2z)
  have h22' := L7F4_step_S14 hn hS13.2 hAn h5d.1 h5d.2.1 h5d.2.2 ha hb hc
  -- n ≡ 1 (mod 6)
  have hmod := L7F5_step_S17 hn h3 ha h22' h19neg h20c
  -- (21) and (22): `n ≡ 1 (mod 6)` exhibits `n = 6l+1`, hence `n − 4 = 3(2l−1)`
  -- with `2l−1` odd — exactly the printed `n − 4 = 3(2p−1)` of S18.
  obtain ⟨l, hl⟩ : ∃ l, n = 6 * l + 1 := ⟨n / 6, by
    have h := Nat.div_add_mod n 6
    omega⟩
  have hl1 : 1 ≤ l := by omega
  have hk : n - 4 = 3 * (2 * l - 1) := by omega
  have hkodd : Odd (2 * l - 1) := ⟨l - 1, by omega⟩
  have h18 := L7F6_step_S18 hkodd hk h10
  have h19' := L7F6_step_S19 hkodd hk h19
  have h20' := L7F6_step_S20 h18 h19'
  have h22 := L7F6_step_S21 h3 h18 h19' hAn
  -- the printed conclusions, in the order of the statement
  refine ⟨hprod, hqa, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h22', hmod⟩
  · simpa [add_comm] using h19
  · simpa using h20
  · simpa [add_comm, mul_comm] using hS12
  · simpa [add_comm, mul_comm] using hS13.1
  · simpa [mul_comm, neg_sub] using hS13.2.neg
  · simpa using h18
  · simpa using h19'
  · simpa using h20'
  · simpa [add_assoc] using h22

end L7
