/-
Chunk `M1-FRAG-04` — the main proof, p. 6 (`P006-R3`) and p. 7 (`P007-R1`): the
`l+j` regrouping that follows the printed (8)-(10).

This file currently carries the leaf's **first step** (S0); the remaining seven
are listed in `pipeline/02-chunks/chunks/M1-FRAG-04.yml` and are not written yet,
so the chunk is IN PROGRESS and nothing here is claimed DONE.

Leaf-boundary note (transcription fact, not an author error): the lane's plan
pencilled `P006-R3` line 1 into `M1-FRAG-03`, but `M1-FRAG-02`'s boundary
revision had already moved (8),(9),(10) out of that leaf, so R3 line 1 — the
triple-sum expansion the whole regrouping starts from — is stated here.

The Vietnamese source text lives in `pipeline/02-chunks/chunks/M1-FRAG-04.yml`
(byte copy of the signed region records), never retyped here.
-/
import Mathlib
import M1F3.Basic

namespace M1F4

/-- The `X`-indexed binomial expansion with a sign, in the shape the print uses:

`(h + (-X))^k = Σ_{j=0}^{k} (-1)^j C(k,j) h^{k-j} X^j`.

`add_pow` gives the `h`-indexed form, so the index is reflected
(`Finset.sum_range_reflect`) and `C(k, k-j)` turned into `C(k,j)`
(`Nat.choose_symm`); the sign comes out of `(-X)^j` by `neg_pow`. This is the same
device as `M1F3.M1F3_add_pow_index`, with the sign the print's `(h - X)` power
needs. -/
lemma M1F4_add_pow_neg (h X : ℤ) (k : ℕ) :
    (h + -X) ^ k
      = ∑ j ∈ Finset.range (k + 1),
          (-1) ^ j * (k.choose j : ℤ) * h ^ (k - j) * X ^ j := by
  rw [add_pow]
  rw [← Finset.sum_range_reflect
    (f := fun m => h ^ m * (-X) ^ (k - m) * (k.choose m : ℤ)) (n := k + 1)]
  rw [show k + 1 - 1 = k by omega]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [Finset.mem_range] at hm
  have hmle : m ≤ k := by omega
  rw [Nat.choose_symm hmle]
  have h1 : k - (k - m) = m := by omega
  rw [h1, neg_pow]
  ring

/-- **S0** — the triple-sum expansion (author p. 6, region `P006-R3`, line 1).

`Σ_{i=0}^{n-1} (h - X)^{n-1-i} (b^n + X)^i
   = Σ_i Σ_j Σ_l (-1)^j C(n-1-i,j) C(i,l) h^{n-1-i-j} b^{n(i-l)} X^{l+j}`

with the printed ranges `i ∈ [0, n-1]`, `j ∈ [0, n-1-i]`, `l ∈ [0, i]`. Both
binomials are expanded with `M1F4_add_pow_neg` / `add_pow`, the two sums are
multiplied out, and `(b^n)^{i-l} = b^{n(i-l)}` is `pow_mul`; the index reflection
is what makes the printed `j` (the power of `X`) the summation index. -/
theorem M1F4_step_S0_triple (n : ℕ) (h b X : ℤ) (_hn : 1 ≤ n) :
    (∑ i ∈ Finset.range n, (h - X) ^ (n - 1 - i) * (b ^ n + X) ^ i)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i),
          ∑ l ∈ Finset.range (i + 1),
            (-1) ^ j * ((n - 1 - i).choose j : ℤ) * (i.choose l : ℤ)
              * h ^ (n - 1 - i - j) * b ^ (n * (i - l)) * X ^ (l + j) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  -- first factor: (h - X)^{n-1-i}, X-indexed with the sign
  rw [show h - X = h + -X by ring, M1F4_add_pow_neg h X (n - 1 - i)]
  -- second factor: (b^n + X)^i, also X-indexed
  rw [add_pow]
  rw [← Finset.sum_range_reflect
    (f := fun m => (b ^ n) ^ m * X ^ (i - m) * (i.choose m : ℤ)) (n := i + 1)]
  rw [show i + 1 - 1 = i by omega]
  -- the two sums multiply out, and the reflected range `range (n-1-i+1)` is the
  -- printed `range (n-i)`
  rw [show n - 1 - i + 1 = n - i by omega]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  rw [Nat.choose_symm (by omega : l ≤ i), ← pow_mul]
  have h3 : i - (i - l) = l := by omega
  rw [h3]
  ring

/-- **The printed exponent split, as a ℕ-valid identity.**

`a^{n(n-1-i)} (n^s abck)^i = (a^{n-1})^{n-i} (n^s bck)^i` for `i + 1 ≤ n`.

**The hypothesis is not cosmetic — Lean found this the hard way.** The print
writes the same right-hand side two ways (`p. 6 R2`: `Σ_i C(n,i) a^{(n-1)(n-i)}
(n^s bck)^i`; `p. 6 R3`: `Σ_i C(n,i) a^{n(n-1-i)} (n^s abck)^i`) and the two are
**equal as ℤ-exponent expressions**, because `n(n-1-i) + i = (n-1)(n-i)`: at
`i = n` the R3 exponent is `-n`, which cancels the bracket's `a^n`. Encoded with
ℕ subtraction the last term silently becomes `a^0·(n^s abck)^n`, i.e. wrong by a
factor `a^n` — the identity is **false** at `i = n`, and this is exactly where
`omega` refused when the lemma was first stated with `i ≤ n`. Hence
`i + 1 ≤ n`: `n - 1 - i` is then exact and the ℕ form matches the ℤ one.
Use the **R2 form** for statements that include `i = n` (it is the plain
`add_pow` form); this lemma is only for the low-order terms (`i ≤ 4`), where the
print itself uses the split. -/
lemma M1F4_absorb (n s i : ℕ) (a b c k : ℤ) (hi : i + 1 ≤ n) :
    a ^ (n * (n - 1 - i)) * ((n : ℤ) ^ s * (a * b * c * k)) ^ i
      = (a ^ (n - 1)) ^ (n - i) * ((n : ℤ) ^ s * (b * c * k)) ^ i := by
  have h_exp : n * (n - 1 - i) + i = (n - 1) * (n - i) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hi
    rw [hm]
    have e1 : i + 1 + m - 1 - i = m := by omega
    have e2 : i + 1 + m - i = m + 1 := by omega
    have e3 : i + 1 + m - 1 = i + m := by omega
    rw [e1, e2, e3]
    ring
  have h_pow : a ^ (n * (n - 1 - i)) * a ^ i = a ^ ((n - 1) * (n - i)) := by
    rw [← pow_add, h_exp]
  -- Rewritten right-to-left with an explicit equation for the first step: a plain
  -- `rw [pow_mul]` would hit the LEFT side too, whose exponent `n*(n-1-i)` is
  -- also a product (that cost round 33).
  rw [show (a ^ (n - 1)) ^ (n - i) = a ^ ((n - 1) * (n - i)) from
    (pow_mul a (n - 1) (n - i)).symm]
  rw [← h_pow]
  rw [show a ^ (n * (n - 1 - i)) * a ^ i * ((n : ℤ) ^ s * (b * c * k)) ^ i
        = a ^ (n * (n - 1 - i)) * (a ^ i * ((n : ℤ) ^ s * (b * c * k)) ^ i) by
      ring]
  rw [← mul_pow]
  rw [show a * ((n : ℤ) ^ s * (b * c * k)) = (n : ℤ) ^ s * (a * b * c * k) by ring]

/-- **S1** — the printed right-hand side (author p. 6, `P006-R3` line 1, second
half; the same line as p. 6 R2's last display).

From the printed `a^n Σ_i (h - X)^{n-1-i}(b^n + X)^i = (a^n + X)^n` it follows
that the triple sum of S0 equals `Σ_i C(n,i) a^{n(n-1-i)} X^i`, `X = n^s abck`.

The print divides by `a^n` implicitly (`a^n Σ = (a^n + X)^n` gives
`Σ = (a^{n-1} + n^s bck)^n`), and over ℤ that needs `a ≠ 0`. That is an **F3**
side condition: it is not printed, and it is supplied here as an explicit
hypothesis rather than derived — `a` is a nonzero integer in the bổ đề 6 setup
(`M1-FRAG-01`), so nothing new is assumed beyond what that chunk established.
Note also that `(a^n + X) = a·(a^{n-1} + n^s bck)` holds outright, so the
cancellation is the only place the side condition is used.

**The right-hand side is stated in the p. 6 R2 form** (`a^{(n-1)(n-i)}`), not the
p. 6 R3 alternate (`a^{n(n-1-i)}`): they are equal as ℤ-exponent expressions but
the R3 form is **false in ℕ-encoded exponents at `i = n`** (there `n - 1 - i`
truncates to `0`, losing a factor `a^n`). See `M1F4_absorb`'s docstring and the
note in `M1_LANE.md` §7. The R2 form is also the plain `add_pow` form, so this
step needs no exponent reshaping at all. -/
theorem M1F4_step_S1_binomial {n s : ℕ} {a b c k h : ℤ} (hn : 1 ≤ n) (ha : a ≠ 0)
    (hmain : a ^ n
        * (∑ i ∈ Finset.range n,
            (h - (n : ℤ) ^ s * (a * b * c * k)) ^ (n - 1 - i)
              * (b ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ i)
      = (a ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ n) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i),
        ∑ l ∈ Finset.range (i + 1),
          (-1) ^ j * ((n - 1 - i).choose j : ℤ) * (i.choose l : ℤ) * h ^ (n - 1 - i - j)
            * b ^ (n * (i - l)) * ((n : ℤ) ^ s * (a * b * c * k)) ^ (l + j))
      = ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℤ) * a ^ ((n - 1) * (n - i))
            * ((n : ℤ) ^ s * (b * c * k)) ^ i := by
  -- the printed cancellation: `a^n Σ = (a·(a^{n-1} + n^s bck))^n`
  have hfac : (a ^ n + (n : ℤ) ^ s * (a * b * c * k))
      = a * (a ^ (n - 1) + (n : ℤ) ^ s * (b * c * k)) := by
    have h1 : a ^ n = a * a ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    rw [h1]
    ring
  have hcancel : (∑ i ∈ Finset.range n,
        (h - (n : ℤ) ^ s * (a * b * c * k)) ^ (n - 1 - i)
          * (b ^ n + (n : ℤ) ^ s * (a * b * c * k)) ^ i)
      = (a ^ (n - 1) + (n : ℤ) ^ s * (b * c * k)) ^ n := by
    rw [hfac, mul_pow] at hmain
    exact mul_left_cancel₀ (pow_ne_zero n ha) hmain
  -- S0 turns the triple sum back into that double sum, then expand the binomial
  rw [← M1F4_step_S0_triple n h b ((n : ℤ) ^ s * (a * b * c * k)) hn, hcancel,
    M1F3.M1F3_add_pow_index (a ^ (n - 1)) ((n : ℤ) ^ s * (b * c * k)) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul]

/-- **Support for S2 — the pointwise filter complement behind the printed
`l+j ≥ 5` split.**

At fixed `(i,j)` the `l`-sum splits into the `5 ≤ j+l` part and its complement,
and this lifts unchanged through the two outer sums. Stated for an arbitrary
summand `f`, so it is a statement about the *index structure* only.

This is the first half of the printed split (author p. 6, `P006-R3` line 2): the
second half — re-indexing the `j+l ≤ 4` part into the fifteen printed natural
ranges `i ∈ [l, n-1-j]` — is designed in `M1-FRAG-04.yml` (step S2) and is not
written yet. -/
lemma M1F4_sum_complement (n : ℕ) (f : ℕ → ℕ → ℕ → ℤ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i),
        ∑ l ∈ Finset.range (i + 1), f i j l)
      = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i),
          ∑ l ∈ Finset.range (i + 1), (if 5 ≤ j + l then f i j l else 0))
        + ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i),
            ∑ l ∈ Finset.range (i + 1), (if ¬(5 ≤ j + l) then f i j l else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hp : 5 ≤ j + l <;> simp [hp]

/-- **S2, second half — the `(j,l,i)` re-indexing of the `l+j ≤ 4` part.**

The printed fifteen boundary sums (author pp. 6-7) are indexed by the pair `(j,l)`
with `j + l ≤ 4`, with the *natural* range `i ∈ [l, n-1-j]`; the triple sum's
`l+j ≤ 4` part indexes the same set of triples by `i` first, with the dependent
ranges `j < n-i`, `l ≤ i`. The two index sets are the **same set in a different
order**, so this is a pure re-indexing: no algebra, no hypothesis on `n`.

Route: flatten both sides to a single sum over a Finset of nested σ-pairs
(`Finset.sum_sigma'`), keep the left side's `l+j ≤ 4` as a `Finset.filter`,
and identify the two filtered index sets by the bijection
`⟨i, ⟨j, l⟩⟩ ↦ ⟨j, ⟨l, i⟩⟩` (`Finset.sum_nbij'`); the membership obligations are
the four Nat facts `j+l ≤ 4 ↔ l ≤ 4-j`, `j < n-i ↔ i+j < n`, `l < i+1 ↔ l ≤ i`,
and `i < n` implied by `i < n-j`. -/
lemma M1F4_reindex (n : ℕ) (f : ℕ → ℕ → ℕ → ℤ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i), ∑ l ∈ Finset.range (i + 1),
        (if j + l ≤ 4 then f i j l else 0))
      = ∑ j ∈ Finset.range 5, ∑ l ∈ Finset.range (5 - j),
          ∑ i ∈ Finset.Ico l (n - j), f i j l := by
  have hL :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i), ∑ l ∈ Finset.range (i + 1),
          (if j + l ≤ 4 then f i j l else 0))
        = ∑ y ∈ ((Finset.range n).sigma
              (fun i => (Finset.range (n - i)).sigma (fun _ => Finset.range (i + 1)))),
            (if y.2.1 + y.2.2 ≤ 4 then f y.1 y.2.1 y.2.2 else 0) := by
    simp only [Finset.sum_sigma']
  have hR :
      (∑ j ∈ Finset.range 5, ∑ l ∈ Finset.range (5 - j),
          ∑ i ∈ Finset.Ico l (n - j), f i j l)
        = ∑ z ∈ ((Finset.range 5).sigma
              (fun j => (Finset.range (5 - j)).sigma (fun l => Finset.Ico l (n - j)))),
            f z.2.2 z.1 z.2.1 := by
    simp only [Finset.sum_sigma']
  have hbij :
      (∑ y ∈ (((Finset.range n).sigma
              (fun i => (Finset.range (n - i)).sigma (fun _ => Finset.range (i + 1)))).filter
              (fun y => y.2.1 + y.2.2 ≤ 4)),
            f y.1 y.2.1 y.2.2)
        = ∑ z ∈ ((Finset.range 5).sigma
              (fun j => (Finset.range (5 - j)).sigma (fun l => Finset.Ico l (n - j)))),
            f z.2.2 z.1 z.2.1 := by
    refine Finset.sum_nbij'
      (fun y => ⟨y.2.1, y.2.2, y.1⟩)
      (fun z => ⟨z.2.2, z.1, z.2.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hy ⊢
      omega
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hz ⊢
      omega
    · rintro ⟨i, j, l⟩ hy
      rfl
    · rintro ⟨j, l, i⟩ hz
      rfl
    · rintro ⟨i, j, l⟩ hy
      rfl
  calc (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i), ∑ l ∈ Finset.range (i + 1),
          (if j + l ≤ 4 then f i j l else 0))
      = ∑ y ∈ ((Finset.range n).sigma
            (fun i => (Finset.range (n - i)).sigma (fun _ => Finset.range (i + 1)))),
          (if y.2.1 + y.2.2 ≤ 4 then f y.1 y.2.1 y.2.2 else 0) := hL
    _ = ∑ y ∈ (((Finset.range n).sigma
            (fun i => (Finset.range (n - i)).sigma (fun _ => Finset.range (i + 1)))).filter
            (fun y => y.2.1 + y.2.2 ≤ 4)),
          f y.1 y.2.1 y.2.2 := by
          rw [← Finset.sum_filter]
    _ = ∑ j ∈ Finset.range 5, ∑ l ∈ Finset.range (5 - j),
          ∑ i ∈ Finset.Ico l (n - j), f i j l := by
          rw [hR]
          exact hbij

/-- **S2 — the printed `l+j ≥ 5` split** (author p. 6 `P006-R3` line 2, continued
on p. 7 `R1` lines 1-2).

The printed display is one sum for each pair `(j,l)` with `j + l ≤ 4` — fifteen of
them, each with the natural range `i ∈ [l, n-1-j]` and the triple sum's own
summand. They are stated here in the natural-range form (verified equal to the
print by `M1-FRAG-04.yml`'s frozen content check, 2026-09-28); the step is the
complement identity `Σ_all f = Σ_{l+j≥5} f + Σ_{l+j≤4} f` with the second sum
re-indexed. Composes the two halves: `M1F4_sum_complement` (the pointwise filter
complement) and `M1F4_reindex` (the `(j,l,i)` re-indexing). -/
theorem M1F4_step_S2_split (n : ℕ) (f : ℕ → ℕ → ℕ → ℤ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i), ∑ l ∈ Finset.range (i + 1), f i j l)
      = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i), ∑ l ∈ Finset.range (i + 1),
          (if 5 ≤ j + l then f i j l else 0))
        + ∑ j ∈ Finset.range 5, ∑ l ∈ Finset.range (5 - j),
            ∑ i ∈ Finset.Ico l (n - j), f i j l := by
  have hD :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i), ∑ l ∈ Finset.range (i + 1),
          (if ¬(5 ≤ j + l) then f i j l else 0))
        = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - i), ∑ l ∈ Finset.range (i + 1),
            (if j + l ≤ 4 then f i j l else 0) := by
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hp : 5 ≤ j + l
    · have h4 : ¬(j + l ≤ 4) := by omega
      simp [hp, h4]
    · have h4 : j + l ≤ 4 := by omega
      simp [hp, h4]
  rw [M1F4_sum_complement n f, hD, M1F4_reindex n f]

end M1F4

-- Evidence for the leaf's DONE flip (all eight steps must reach this state):
-- permitted axioms only, and no `sorryAx`.
#print axioms M1F4.M1F4_step_S0_triple
#print axioms M1F4.M1F4_step_S1_binomial
#print axioms M1F4.M1F4_sum_complement
#print axioms M1F4.M1F4_reindex
#print axioms M1F4.M1F4_step_S2_split
