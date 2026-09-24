# Encoding map — the author's terms → Lean/Mathlib

Purpose: the next lemma chunk must not re-derive the same dictionary. This
file is **append-only per chunk** and holds two things:

1. **§A** the PDF's notation conventions (they recur in every lemma);
2. **§B** per-chunk tables: author step → Lean declaration → the lemmas
   that did the work, plus **copy-paste proof patterns** that already
   compiled.

Division of labour with the neighbouring docs:

| Doc | Holds |
|---|---|
| `pipeline/03-lean/MATHLIB_API_LESSONS.md` | API pitfalls (what fails, exact signatures, workarounds) |
| `pipeline/03-lean/ENCODING_MAP.md` (this) | term/notation mapping + reusable proof patterns |
| `pipeline/02-chunks/chunks/*.yml` | the literal transcription + ordered step map (S0…Sn) |
| `.github/skills/fermat-lean-mathlib/SKILL.md` | toolchain, container loop, search ladder |

Rule of thumb: a *fact about a lemma* goes in MATHLIB_API_LESSONS.md; a
*fact about how the paper's words become a statement* goes here.

---

## §A. Author notation → Lean (global, applies to all seven lemmas)

| Author (PDF) | Meaning | Lean encoding | Watch out |
|---|---|---|---|
| `(a, b)` | gcd | `Int.gcd a b : ℕ` | ℕ-valued, **not** ℤ |
| `(a, b, c)` | triple gcd, "no common divisor" | `Int.gcd a ((Int.gcd b c : ℕ) : ℤ) = 1` | nesting needs the cast |
| `a ⋮ b` | `a` is divisible by `b` | `b ∣ a` | **argument order flips** vs. the glyph — transcription-critical |
| `b ∤ a` | not divisible | `¬ b ∣ a` | |
| `a ≡ b (mod n)` | congruence | `(a - b : ℤ) ≡ 0 [ZMOD n]`, or a `ZMod n` equality | see MATHLIB_API_LESSONS.md §Int.ModEq |
| `a ≢ 0 (mod n)` | not divisible by `n` | `¬ (n : ℤ) ∣ a` | |
| `aⁿ` | power | `a ^ n` | |
| `xⁿ + yⁿ = zⁿ (1)` | Fermat equation | `x ^ n + y ^ n = z ^ n` | the label `(1)` becomes a hypothesis name |
| `(1')`, `(1'')` | derived equation | its own hypothesis/binding | never invent it — it is an author step |
| `ℤ*` | nonzero integers | `x ≠ 0`, per component | |
| "nghiệm nguyên khác không" | every coordinate nonzero | `a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0` | |
| `n ≥ 3` / "n lớn hơn 2" | | `3 ≤ n` | identical for `n : ℕ` |
| "n là số nguyên tố (lẻ)" | prime (odd) | `hn : Nat.Prime n` (+ `3 < n` to get `Odd n`) | `Nat.Prime.eq_two_or_odd` returns `n % 2 = 1`, **not** `Odd n` |
| "Giả sử …" | assume | `intro`, or a theorem hypothesis | |
| "Suy ra" / "Khi đó" | hence | the next author step | |
| "Chứng minh tương tự" | symmetric instance | reuse the step theorem with **permuted** args | the permutation can hide a sum→difference switch: see §B L1 S6 |
| "vô lý" | absurd | derive `False` | |
| "(đpcm)" | QED | end of assembly theorem | |
| "Bổ đề k" | Lemma k | chunk id `Lk-01`, theorem `Lk_bo_de_k` | |

Conventions this project fixed on (keep them for the next chunks):

- One chunk YAML per lemma, with **two** records: literal transcription and
  the ordered step map `S0…Sn` (one entry per author inference).
- **One author step = one named Lean declaration**, compiled and classified
  (F1–F4/S1) before the next step is written. Steps that are pure
  assumptions (S0, S2 in L1) collapse into the following inference.
- Final assembly theorem named after the lemma (`L1_bo_de_1`), chaining the
  step theorems in the author's order.
- `#print axioms` on every declaration; only `propext`,
  `Classical.choice`, `quot.sound` allowed.
- An author hypothesis carried for faithfulness but unused by a step keeps
  its place with a `_`-prefixed name plus a docstring note (L1's `_hn`).

---

## §B. Chunk L1-01 — bổ đề 1 (DONE, all steps S1)

Source: statement p. 1, proof p. 2. Evidence:
`03-lean/L1-01_compile_20260925.log` (EXIT:0, no `sorry`), `04-sympy/test_l1_01.py`.

| Author step | Text (p. 2) | Lean declaration |
|---|---|---|
| S0+S1 | "…(u₀,v₀,t₀) = d… u₀ = ud, v₀ = vd, t₀ = td … (u,v,t) = 1 … uⁿ+vⁿ = tⁿ (1'')" | `L1.L1_reduce_coprime` |
| S2+S3 | "Giả sử (u, v) = d', từ (1'') suy ra tⁿ ⋮ d'ⁿ" | `L1.L1_step_S2_S3` |
| S4 | "suy ra t ⋮ d'" | `L1.L1_step_S4` |
| S5 | "mà (u, v, t) = 1 nên d′ = 1. Vậy (u, v) = 1." | `L1.L1_step_S5` |
| S6 | "Chứng minh tương tự ta cũng có (u, t) = (t, v) = 1." | `L1.L1_step_S6` |
| assembly | whole bổ đề 1 | `L1.L1_bo_de_1` |

### Reusable results from this chunk

```lean
-- pairwise-coprime solution exists (the chunk's headline output):
L1.L1_bo_de_1 {n : ℕ} (hn : 3 ≤ n) {u₀ v₀ t₀ : ℤ}
    (hu₀ : u₀ ≠ 0) (hv₀ : v₀ ≠ 0) (ht₀ : t₀ ≠ 0)
    (hsol : u₀ ^ n + v₀ ^ n = t₀ ^ n) :
    ∃ u v t : ℤ, u ≠ 0 ∧ v ≠ 0 ∧ t ≠ 0 ∧ u ^ n + v ^ n = t ^ n ∧
      Int.gcd u v = 1 ∧ Int.gcd u t = 1 ∧ Int.gcd v t = 1

-- generic and directly reusable (any `d` dividing all three coords):
L1.L1_step_S5 {u v t : ℤ} {d : ℕ}
    (hu : (d : ℤ) ∣ u) (hv : (d : ℤ) ∣ v) (ht : (d : ℤ) ∣ t)
    (hcop : Int.gcd u ((Int.gcd v t : ℕ) : ℤ) = 1) : d = 1

L1.L1_step_S4 {n : ℕ} (hn : n ≠ 0) {d : ℕ} {t : ℤ}
    (h : (d : ℤ) ^ n ∣ t ^ n) : (d : ℤ) ∣ t

L1.L1_step_S2_S3 {n : ℕ} {u v t : ℤ} (hsol : u ^ n + v ^ n = t ^ n) :
    ((Int.gcd u v : ℕ) : ℤ) ^ n ∣ t ^ n
```

Any later lemma that needs "divide a solution by its gcd", "a common
divisor of a coprime triple is 1", or "`dⁿ ∣ tⁿ` gives `d ∣ t`" should
import/reuse these rather than re-derive them.

### Copy-paste proof patterns (all compiled at this pin)

**P1 — a gcd divides its components** (`Int.gcd` is ℕ-valued):

```lean
have hdvdv : ((Int.gcd u v : ℕ) : ℤ) ∣ u := Int.gcd_dvd_left u v
have hdvdt : ((Int.gcd u v : ℕ) : ℤ) ∣ v := Int.gcd_dvd_right u v
-- through the nesting: gcd_dvd_right to the inner gcd, then trans
have h : (D : ℤ) ∣ t₀ := dvd_trans hDdvdG hGdvdt
```

**P2 — gcd is *greatest*** (pick the ℤ-out or ℕ-out form by the goal):

```lean
-- goal `↑d ∣ ↑(gcd v t)`  (ℤ divisibility output):
have h1 : (d : ℤ) ∣ ((Int.gcd v t : ℕ) : ℤ) := Int.dvd_coe_gcd hv ht
-- goal `d ∣ Int.gcd v t`   (ℕ divisibility output):
have h2 : d ∣ Int.gcd v t := Int.dvd_gcd hv ht
```

**P3 — divide a triple by its gcd** (author's "u₀ = ud, v₀ = vd, t₀ = td"):

```lean
set D : ℕ := Int.gcd u₀ ((Int.gcd v₀ t₀ : ℕ) : ℤ) with hD
obtain ⟨u, hu⟩ := hDdvd₀        -- hu : u₀ = ↑D * u   (Dvd unfolds to ∃)
have hu_ne : u ≠ 0 := by        -- divide nonzero by nonzero
  intro h
  rw [h, mul_zero] at hu
  exact hu₀ hu
-- push the equation through the power, then cancel dⁿ ≠ 0:
have hsol' : u ^ n + v ^ n = t ^ n := by
  have key : ((D : ℤ) ^ n) * (u ^ n + v ^ n) = ((D : ℤ) ^ n) * t ^ n := by
    rw [mul_add, ← mul_pow, ← mul_pow, ← mul_pow]
    rw [← hu, ← hv, ← ht]
    exact hsol
  exact mul_left_cancel₀ (pow_ne_zero n (by exact_mod_cast hDne)) key
```

**P4 — "no common divisor" ⇒ any common divisor is 1** (author's
"mà (u, v, t) = 1 nên d′ = 1"):

```lean
-- maximality of the author's `d`, built from Int.dvd_gcd twice:
have hmax : ∀ m : ℕ, (m : ℤ) ∣ u₀ → (m : ℤ) ∣ v₀ → (m : ℤ) ∣ t₀ → m ∣ D
-- then: if e is a common divisor, e*d is too, so e*d ∣ d, cancel d ≠ 0,
--       and finish with Nat.dvd_one.mp.
```

**P5 — `d ^ n ∣ t ^ n ⇒ d ∣ t`** (routes through ℕ + factorization; needs
`n ≠ 0`, which the author's `n ≥ 3` supplies):

```lean
have hN : d ^ n ∣ t.natAbs ^ n := by
  have h' := (Int.natAbs_dvd_natAbs).mpr h
  simpa only [Int.natAbs_pow, Int.natAbs_natCast] using h'
-- with hd : d ≠ 0, hB : t.natAbs ≠ 0 (branch on the zero cases first):
refine (Nat.factorization_le_iff_dvd hd hB).mp ?_
have h1 : (d ^ n).factorization ≤ (t.natAbs ^ n).factorization :=
  (Nat.factorization_le_iff_dvd (pow_ne_zero n hd) (pow_ne_zero n hB)).mpr hN
simp only [Nat.factorization_pow] at h1
simp only [Finsupp.le_def] at h1 ⊢
intro p
have hp := h1 p
simp only [Finsupp.smul_apply, nsmul_eq_mul] at hp
exact Nat.le_of_mul_le_mul_left hp (Nat.pos_iff_ne_zero.mpr hn)
-- and back to ℤ:
exact (Int.natAbs_dvd_natAbs).mp (by simpa only [Int.natAbs_natCast] using hdvd)
```

**P6 — spelling out "chứng minh tương tự"**: reuse the step theorem with
permuted coordinates, and check whether the *relation* also permutes. For
L1 S6 the sum `uⁿ + vⁿ = tⁿ` gave `tⁿ − uⁿ = vⁿ` and `vⁿ − tⁿ = −uⁿ`, so the
instances needed `dvd_sub` and `dvd_neg`:

```lean
have h4 : t ^ n - u ^ n = v ^ n := by rw [← hsol]; ring
rw [h4] at h3
exact L1_step_S4 hn h3
```

### Method note for the sympy screen (reusable)

For `n ≥ 3` the Fermat equation has **no** nonzero integer solution, so no
witness search can exercise bổ đề 1, 2, 6, 7's hypotheses; a boxed search
returns 0 solutions (`test_l1_01.py`, n ∈ {5,7,11,13}). Screen the
**inferences** instead (each `Sᵏ` on small ranges, and on `n = 1, 2` where
solutions do exist), and say so in the chunk — otherwise "sympy PASS" looks
stronger than it is.

---

## §C. Extending this file for the next chunk

1. Add a `## §B. Chunk Lk-01 — …` section with the same four parts: step
   table, reusable results, patterns, screen note.
2. Add rows to §A only for notation §A does not yet cover.
3. Move any pattern that other chunks also need (P1–P5 are candidates) to
   the top of its section so it is not re-derived.
4. Record the classification outcome (F1–F4/S1) per step in the chunk YAML,
   not here; here record only the mapping and the surviving code shapes.

Last updated: 2026-09-25, after L1-01 (bổ đề 1) reached DONE.
