# Mathlib naming + pitfall digest (this repo, this pin)

Covers: guessing lemma names, the tactics table for THIS project's math
(elementary number theory, ℤ/ℕ/`ZMod`), and the error→fix table.
Source of truth for API pitfalls: `pipeline/03-lean/MATHLIB_API_LESSONS.md`
— append every newly learned pitfall there, then fold it into this file.

## Naming conventions — guess the lemma before you search

Theorems/props: `snake_case`. Types/classes: `UpperCamelCase`. Functions
are named after their return value. Full rules:
<https://leanprover-community.github.io/contribute/naming.html>

Symbol dictionary (most relevant here):

| symbol | name in lemma names |
|---|---|
| `+` `*` `-` `^` | `add` `mul` `sub` `pow` |
| `∣` | `dvd` |
| `≤` `<` | `le` `lt` (Mathlib never states `≥`/`>`; `ge`/`gt` appear only when args are swapped vs. another relation) |
| `=` `≠` `↔` | `eq` `ne` `iff` |
| `→` | `of` (conclusion first, hypotheses follow) |
| `0` `1` `⁻¹` | `zero` `one` `inv` |

Pattern fragments:

- `X_of_Y` — conclusion from hypothesis: `le_of_lt`, `pos_of_ne_zero`, `ne_zero_of_dvd`.
- `X_iff_Y` — biconditional: `modEq_zero_iff_dvd`.
- Axiomatic suffixes: `comm`, `assoc`, `left_comm`, `refl`, `symm`,
  `trans`, `antisymm`, `inj`, `cancel`.
- The name reads in syntax-tree order of the statement — decode the
  statement first, then assemble the name.

Example workflow: goal `a ≡ b [ZMOD n] → a % n = b % n` → guess
`Int.ModEq...` → verify with `#check` (batch!) or local grep.

## Tactics decision table (scoped to this project's math)

| Goal shape | First try | Notes |
|---|---|---|
| Numeric equality (`2 + 2 = 4`, `7^3 = 343`) | `norm_num`, `decide` | `decide` only for tiny `Nat`/`Bool` |
| Linear arith over `ℤ`/`ℕ` | `omega` | never works on `ZMod` equalities |
| Linear arith with hypotheses | `linarith` | same `ZMod` restriction |
| Nonlinear with known bounds | `nlinarith [sq_nonneg x, ...]` | feed hints explicitly |
| Ring algebra (any `CommRing`, incl. `ZMod n`) | `ring` | works in `ZMod` |
| Field algebra in `ZMod p` | `field_simp` then `ring` | |
| Cast/congruence gaps (`(a : ZMod n) = b` vs `a ≡ b`) | `exact_mod_cast`, `norm_cast`, `push_cast` | often closes automatically |
| Finish from library | `exact?` / `apply?` | see references/search.md |
| Rewrite by unknown lemma | `rw?` | |
| Discover `simp` set | `simp?` | outputs reusable `simp only [...]` |
| Conjunction / structure | `constructor`, `refine ⟨_, ?_⟩` | |
| Existential witness | `refine ⟨w, ?_⟩` | |

## `ZMod` rules learned in this repo (each cost compile time)

1. **`linarith`/`omega` fail on `ZMod` equalities** — lift to `ℤ` first
   via `ZMod.intCast_zmod_eq_zero_iff_dvd` (0-case) or `norm_cast` /
   `exact_mod_cast` (general), then reason in `ℤ`.
2. **Variable modulus needs `Fact (Nat.Prime n)`** for the field instance;
   `hn : Nat.Prime n` alone may not synthesize `Field (ZMod n)`.
3. **`mul_right_cancel₀` fails** (missing `IsRightCancelMulZero`) — use
   `mul_left_cancel₀` / `eq_of_mul_eq_mul_left` (Field API).
4. **Test with `n = 7` first** when variable-`n` fails: separates API
   problems from logic errors.
5. **`pow_mul` argument order**: `a ^ (m * n)` does not unify with
   `(a ^ m) ^ n` in `rw` — align with `show`/`calc` + `mul_comm`, or use
   `← pow_mul`.
6. `ring`/`field_simp` work in `ZMod`; arithmetic decision procedures do not.

## Error → fix table

| Lean error | Fix |
|---|---|
| `failed to synthesize instance` | add `Fact (Nat.Prime n)` (`haveI`), or pick a lemma stated for the type you actually have |
| `type mismatch ... at ↑` cast errors | `exact_mod_cast` / `norm_cast`, or state the lemma at the cast level |
| `rewrite tactic failed, pattern ... not found` | goal shape ≠ lemma shape — align term order (`mul_comm`, `show`) before `rw` |
| `unknown identifier Foo` | missing import / wrong namespace — `#check @Foo` in a batch to confirm the name |
| `no goals` / leftover goals after `simp` | `simp` rewrote more than intended — switch to `simp?` to capture the exact lemma list |

## Trust boundaries

- Acceptable axioms: `Classical.choice`, `propext`, `quot.sound`.
  Verify with `#print axioms <thm>`.
- A theorem that compiles with `sorry` is NOT verified — `sorry` is
  scaffolding only, and for this project a `sorry` on an author step
  means the chunk is not DONE.
- Docs site (mathlib4_docs) tracks a possibly *newer* Mathlib than our
  pin (`v4.35.0-rc2`, rev `06535612…`). When docs and local source
  disagree, the local source tree is the truth — grep it.
