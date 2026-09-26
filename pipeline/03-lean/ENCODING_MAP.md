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

### Chunk file skeleton (`Lk/Basic.lean`) — the de-facto template

There is no separate `.lean` template file: the newest DONE chunk is the
template (`03-lean/L3/Basic.lean`). Its shape:

```lean
import Mathlib   -- plus `import Lj.Basic` when this chunk cites another chunk

/-!
# Lemma k (bổ đề k) — the author's proof, steps S0–Sn

Source: `PROOF_of_FERMAT.pdf`
  * statement: p. P, lemma k of section A;
  * proof: p. Q, section "k. Chứng minh bổ đề k".

The literal Vietnamese transcription and the ordered step map live in
`pipeline/02-chunks/chunks/Lk-01.yml` (`source_text`, `author_steps`).
One named declaration per author step (English paraphrase):

  S0     <author sentence, one line>          -> Lk_step_S0
  S1+S2  <author sentence, one line>          -> Lk_step_S1_S2
-/

namespace Lk

/-- **S0** (p. Q): <the author's inference, with its source line>. -/
theorem Lk_step_S0 … := by …

-- … S0…Sn in the author's order, one declaration each, bunched exactly as the
-- chunk YAML's `author_steps` bunch them …

/-- Assembly: bổ đề k, chaining the step theorems in the author's order
(`(đpcm)`). -/
theorem Lk_bo_de_k … := by
  -- one comment per author step naming it, then the step theorem's callsite
  …

#print axioms Lk.Lk_step_S0
-- … one line per declaration, assembly last …

end Lk
```

What the skeleton encodes (each item cost compile time in L1–L3):

- **English docstrings**; the literal transcription lives only in the chunk
  YAML's `source_text` (AGENTS.md text-fidelity rule).
- A hypothesis the author states but a step does not consume keeps its place
  in the signature, named `_h…`, with a docstring note (`_hn`, `_hb`).
- Docstring headers cite page and step label, so a reader can move from a
  Lean declaration back to the PDF without the YAML.
- `#print axioms` on every declaration (assembly last); only `propext`,
  `Classical.choice`, `Quot.sound` may appear.
- Compile through `proof/compile_lean.sh Lk/Basic.lean`; append each round to
  `03-lean/Lk-01_compile_YYYYMMDD.log` under a `=== round N: … ===` marker and
  put the *diagnosis* in the marker — the F2 items in
  `MATHLIB_API_LESSONS.md` cite those lines later.
- Before the first step, spend one round on a **probe file** (untracked, e.g.
  `LkProbe.lean`) holding `#check @` for every lemma you intend to cite —
  instead of one round per wrong name.

### Reusing a DONE chunk (wiring in place since 2026-09-26)

- Record the citation as `depends_on: [<id>]`; `progress.py` refuses a
  dependency that is not DONE. Do **not** redo a DONE chunk's
  transcription, step map, sympy screen or F1–F4/S1 classification — that
  is exactly what DONE certifies.
- At the Lean level, reuse means **`import` the producing module**, never
  paste its statements or proofs into another file. A pasted copy costs a
  second elaboration of the same proof and, worse, can drift from the
  verified original — the thing you cite stops being the thing that was
  verified. (The speed part of that argument is weak here: see the measured
  cost model below, where the `import Mathlib` floor dominates.)
- L1's first real consumer is **not** L7. The PDF cites bổ đề 1 only at
  p. 6 ("áp dụng bổ đề 1", main theorem, case n > 11), and bổ đề 6 takes
  `(u, v) = (u, t) = (v, t) = 1` as a hypothesis, i.e. bổ đề 1's output.
  `L7-FRAG-01` cites bổ đề 5c/5đ instead, so it takes no L1 edge.
- L1's conclusion is an `∃`; a consumer destructures it (see the assembly
  in `L1_bo_de_1`). Destructuring is glue work, not re-verification.

**Wiring status — DONE 2026-09-26** (first consumer: L4-01, bổ đề 4, which
cites bổ đề 3). `proof/compile_lean.sh` now performs both halves:

- it syncs the repo-tracked `pipeline/03-lean/lakefile.toml` into the
  package, so the `[[lean_lib]]` declarations cannot drift from the repo
  and a recreated `lake-work` volume regains them. `Common`, `L1`, `L2`,
  `L3` are declared, each with an explicit `roots` (a `lean_lib` named `L3`
  would otherwise look for `L3.lean`, while our module is `L3/Basic.lean`);
- it compiles with `lean -o <package>/.lake/build/lib/lean/<relative>.olean`,
  so every successfully compiled chunk is published as an importable module
  at no extra elaboration cost. It deletes the previous olean first, so a
  *failed* compile cannot leave a stale artifact for a consumer to import.

A consumer therefore writes `import L3.Basic` and cites `L3.L3_bo_de_3` (or
a step theorem); no separate `lake build` step is needed. Verified mechanism
2026-09-26: `lean -o` on a trivial module then `import` of it from a second
file (olean written in 4 s, no Mathlib), plus a real round on
`L3/Basic.lean` through the updated harness
(`03-lean/L3-01_compile_20260926.log`, round 12).

**Cost model (measured; corrects the older claim that a consumer pays
"minutes" for a paste).** The per-round floor in this container is the
`import Mathlib` elaboration — ~150–350 s per round across L1–L3 — and a
chunk's own ~300 lines add only seconds. A **second session compiling at the
same time roughly triples it**: the harness validation recompile of
`L3/Basic.lean` took 922 s while the L4 session was also compiling
(2026-09-26). Two consequences: (a) the reason to import rather than paste is
correctness, not speed; (b) the real lever on cost is the *number of rounds*,
so batch every `#check` probe into one file, keep the one-step loop's
discipline of not compiling speculative later steps, and do not run two
compile-heavy sessions at once if wall-clock matters.

**Olean staleness caveat.** The published olean is a by-product of the last
*successful* compile of that path. Editing a producer chunk without
recompiling it leaves a consumer importing the older proof; recompiling a
freshly edited chunk through `compile_lean.sh` refreshes it. This only bites
while a chunk is under development — a DONE chunk's source is frozen by its
evidence block. `Main.lean` is the aggregate root; it requires the oleans of
the chunks it lists, and it deliberately keeps the parked `Pilot` scratch
module (2 sorries, L7-FRAG-01/Q-001) out of the verified set.

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

## §B. Chunk L2-01 — bổ đề 2 (DONE, all steps S1)

Source: statement p. 1, proof p. 2 §2. Evidence:
`03-lean/L2-01_compile_20260925.log` (EXIT:0, no `sorry`, no warnings),
`04-sympy/test_l2_01.py`.

| Author step | Text (p. 2) | Lean declaration |
|---|---|---|
| S0 | "Giả sử tồnă să întreg dôvă k₀ … x^{nk₀} + y^{nk₀} = z^{nk₀} cu nghiệm întreg khác genom x = u, y = v, z = t" | hypothesis of `L2.L2_step_S1` |
| S1 | "… u^{nk₀} + v^{nk₀} = t^{nk₀} ⇔ (u^{k₀})ⁿ + (v^{k₀})ⁿ = (t^{k₀})ⁿ" | `L2.L2_step_S1` (power identity, forward direction) |
| S2 | "suy ra PT xⁿ + yⁿ = zⁿ cu nghiệm întreg khác genom x = u^{k₀}, y = v^{k₀}, z = t^{k₀}" | conclusion of `L2.L2_step_S1` |
| S3 | "diễneăs trái cu giã thiete" (contrapositive) | `L2.L2_bo_de_2` (assembly) |

### Reusable results from this chunk

```lean
-- power identity in the RIGHT direction (the one that compiled):
--   u ^ (k * n)  ->  (u ^ k) ^ n     by  rw [pow_mul]
L2.L2_step_S1 {n k : ℕ} {u v t : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (ht : t ≠ 0)
    (hsol : u ^ (k * n) + v ^ (k * n) = t ^ (k * n)) :
    u ^ k ≠ 0 ∧ v ^ k ≠ 0 ∧ t ^ k ≠ 0 ∧
      (u ^ k) ^ n + (v ^ k) ^ n = (t ^ k) ^ n

-- the lemma itself (contrapositive wrap):
L2.L2_bo_de_2 {n k : ℕ} (_hn : 3 ≤ n) (_hk : k ≠ 0)
    (hno : ¬ ∃ u v t : ℤ, u ≠ 0 ∧ v ≠ 0 ∧ t ≠ 0 ∧ u ^ n + v ^ n = t ^ n) :
    ¬ ∃ u v t : ℤ, u ≠ 0 ∧ v ≠ 0 ∧ t ≠ 0 ∧
      u ^ (k * n) + v ^ (k * n) = t ^ (k * n)
```

### Copy-paste proof patterns (all compiled at this pin)

**P7 — "raising a solution's coordinates" (bổ đề 2's whole content):**

```lean
-- goal: (u ^ k) ^ n + (v ^ k) ^ n = (t ^ k) ^ n  from
--       hsol : u ^ (k * n) + v ^ (k * n) = t ^ (k * n)
rw [pow_mul, pow_mul, pow_mul] at hsol
exact hsol
```

`pow_mul` at this pin (`Mathlib/Algebra/Group/Pow/Monoid.lean:459`):
`a ^ (m * n) = (a ^ m) ^ n`. The exponent in the paper is written
`nk₀`; Lean's `k * n` matches `?m * ?n` directly — NO `mul_comm` needed
for the rewrite (the `mul_comm k n` I first added was harmless but
redundant).

- Nonzero preservation: `pow_ne_zero k hu : u ^ k ≠ 0`.
- Contrapositive assembly: `intro h; obtain ⟨u, v, t, hu, hv, ht, hsol⟩
  := h` then hand the obtained witnesses to the step theorem and
  `exact hno ⟨u ^ k, v ^ k, t ^ k, …⟩`.
- `_hn` / `_hk` naming: the linter flags hypotheses the proof never
  must reference; the author's `n ≥ 3` / `k ∈ ℕ*` are carried for
  faithfulness, so they get the `_` prefix (same pattern as L1's `_hn`).

### Method note for the sympy screen (reusable)

Like every lemma with `n ≥ 3`, bổ đề 2's hypotheses admit no witness in
a boxed search (`test_l2_01.py`, n ∈ {5,7,11,13}, k ∈ {2,3,5}: 0
candidates). Two ways to screen the *inference* anyway:

1. The transformation `(u^k)^n = u^(k*n)` does not depend on `n` —
   screen it on **real witnesses at n = 1**: 3644 lifted triples
   checked (k ∈ {1,2,3,5}).
2. Direct identity check on the box (1000 cases).

---

## §B. Chunk L3-01 — bổ đề 3 (DONE, all steps S1)

Source: statement p. 1 (section A, lemma 3), proof p. 2 §3. Evidence:
`03-lean/L3-01_compile_20260926.log` (EXIT:0, no `sorry`, no warnings;
`#print axioms` on all eight declarations = propext, Classical.choice,
Quot.sound only), `04-sympy/test_l3_01.py` PASS.

| Author step | Content (English; literal text in the chunk YAML) | Lean declaration |
|---|---|---|
| S0 | divide `a` and `c` by `c'_1 = (a,c)`; quotients `a_1`, `c'_2` coprime | `L3.L3_step_S0` |
| S1+S2 | from `ab = c^n`: `c'_1·a_1·b = c'_1^n·c'_2^n`, hence `a_1·b = c'_1^{n-1}·c'_2^n` | `L3.L3_step_S1_S2` |
| S3+S4 | `b ∣ c'_1^{n-1}·c'_2^n`; `(c'_1,b) = 1` gives `c'_2^n = k·b`, `k ≠ 0` | `L3.L3_step_S3_S4` |
| S5 | cancel `b`: `a_1 = k·c'_1^{n-1}` | `L3.L3_step_S5` |
| S6+S7+S8 | `a_1^n = k^n·c'_1^{n(n-1)}`, so `k ∣ a_1^n` and `k ∣ c'_2^n` | `L3.L3_step_S6_S8` |
| S9+S10 | `(a_1,c'_2) = 1 ⟹ (a_1^n,c'_2^n) = 1`, hence `\|k\| = 1` | `L3.L3_step_S9_S10` |
| S11 | `c_1 = k·c'_1`, `c_2 = k·c'_2`: nonzero, coprime, `c = c_1·c_2`, `a = c_1^n`, `b = c_2^n` | `L3.L3_step_S11` |
| assembly | whole lemma 3 | `L3.L3_bo_de_3` |

### Reusable results from this chunk

```lean
-- the lemma itself (statement p. 1):
L3.L3_bo_de_3 {a b c : ℤ} {n : ℕ} (hn : Odd n) (hn0 : 0 < n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a * b = c ^ n) (hgcd_ab : Int.gcd a b = 1) :
    ∃ c1 c2 : ℤ, c1 ≠ 0 ∧ c2 ≠ 0 ∧ Int.gcd c1 c2 = 1 ∧
      c = c1 * c2 ∧ a = c1 ^ n ∧ b = c2 ^ n

-- directly reusable pieces:
L3.L3_step_S0 {a c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) :
    ∃ a1 c2' : ℤ, Int.gcd a1 c2' = 1 ∧
      a = ↑(Int.gcd a c) * a1 ∧ c = ↑(Int.gcd a c) * c2'      -- (drops `hc` in the proof)

L3.L3_step_S9_S10 {n : ℕ} {a1 c2' k : ℤ} (hgcd : Int.gcd a1 c2' = 1)
    (h7 : k ∣ a1 ^ n) (h8 : k ∣ c2' ^ n) : Int.natAbs k = 1
```

Every later lemma that needs "divide a pair by its gcd" (bổ đề 4 does, on
`(a,c)` … `(h,l)`), "coprimality survives powers", "a common divisor of two
coprime coprime-power facts is `±1`", or "`k ∣ x`, `k ∣ y`, `(x,y) = 1`
gives `|k| = 1`" should import/reuse these rather than re-derive them.
Consumers: bổ đề 4 (p. 2 §4) applies lemma 3 to `h·l = r^n` with
`(h,l) = 1`; bổ đề 7's proof applies it at `u+v = c^n` and `t−v = b^n`.

### Copy-paste proof patterns (all compiled at this pin)

**P8 — the "divide by the gcd" step** (author's `(a,c) = c'_1`):

```lean
have hpos : 0 < Int.gcd a c := by
  rw [Int.gcd_def]
  exact Nat.gcd_pos_of_pos_left c.natAbs
    (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha))
obtain ⟨a1, c2', hg, h1, h2⟩ := Int.exists_gcd_one hpos
-- h1 : a = a1 * ↑(Int.gcd a c), h2 : c = c2' * ↑(Int.gcd a c), hg : Int.gcd a1 c2' = 1
```

**P9 — Euclid + coprime powers in ℤ** (author's S4 and S9):

```lean
have hcop : IsCoprime b ((Int.gcd a c : ℤ)) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]   -- lands on the ℕ-side fact
  exact hg_b                                        -- Int.gcd (↑g) b = 1
have hcop_pow : IsCoprime b ((Int.gcd a c : ℤ) ^ (n - 1)) := hcop.pow_right
have hb_dvd_c2 : b ∣ c2' ^ n := hcop_pow.dvd_of_dvd_mul_left hb_dvd
-- and the same-power instance:  IsCoprime (a1^n) (c2'^n) := hcop.pow
```

**P10 — `|k| = 1`, then `k^n = k` for odd `n`** (author's S10/S11):

```lean
have hk_sq : k * k = 1 := Int.isUnit_mul_self (Int.isUnit_iff_natAbs_eq.mpr hkab)
have hkn : k ^ n = k := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hk_sq with h | h <;> rw [h]
  · rw [one_pow]
  · rw [Odd.neg_one_pow hn]        -- hn : Odd n
```

**P11 — the ℤ-gcd rewrite hazard (do not re-learn this):** if `h : a = …`
(or `c = …`) and the goal still contains `Int.gcd a c`, a plain `rw [h]`
rewrites *inside the gcd argument* and destroys the goal. Use `calc`
(after proving the multiplicativity with `mul_comm`) or
`conv_lhs => rw [h]` / `conv_rhs => rw [h]`. Full detail:
`MATHLIB_API_LESSONS.md` § Session 2026-09-26 items 2–3.

### Method note for the sympy screen (reusable — opposite of L1/L2/L6/L7)

**Lemma 3's hypotheses are satisfiable for every odd `n`** (`a = c1^n`,
`b = c2^n`, `c = c1·c2` with `(c1,c2) = 1`), so unlike the FLT-equation
lemmas this screen tests every author step on **real instances**:
`test_l3_01.py` runs the whole S0–S11 chain plus the statement's witness
construction on 2184 structured instances and 2264 boxed instances
(`n ∈ {1,3,5,7,11,13}`, which includes the schema-required
{5,7,11,13}), and exhibits the even-`n` counterexample
(`a = -4, b = -9, c = 6, n = 2`) that shows the author's oddness
hypothesis is load-bearing. When a later lemma's hypotheses *are*
satisfiable, prefer this instance-based screen over a vacuity note.

---

## §C. Extending this file for the next chunk

1. Add a `## §B. Chunk Lk-01 — …` section with the same four parts: step
   table, reusable results, patterns, screen note.
2. Add rows to §A only for notation §A does not yet cover.
3. Move any pattern that other chunks also need (P1–P5 are candidates) to
   the top of its section so it is not re-derived.
4. Record the classification outcome (F1–F4/S1) per step in the chunk YAML,
   not here; here record only the mapping and the surviving code shapes.

Last updated: 2026-09-26, after L3-01 (bổ đề 3) reached DONE (L1-01, L2-01 §B above).
