-- Probe for chunk M1-LANE — the main proof (PROOF_of_FERMAT.pdf pp. 6–33,
-- printed section `D. CHỨNG MINH ĐỊNH LÝ LỚN FERMAT`). This is the single
-- batched name round the M1 lane spends before its first author step
-- (ENCODING_MAP §A "Probe archive": one batched probe round beats one round
-- per wrong name).
--
-- chunk id:        M1-LANE
-- date:            2026-09-28
-- toolchain:       lean 4.35.0-rc2 / lake 5.0.0
-- mathlib rev:     v4.35.0-rc2 (065356127b1dc001f66b7283ce0ce2c40555aa55)
-- run command:     sh proof/compile_lean.sh probes/M1-LANE.probe.lean
-- log:             probes/M1-LANE.probe.log
-- STATUS:          VERIFIED — round 1, 2026-09-28: EXIT=0, 355 s, zero errors
--                  (log: probes/M1-LANE.probe.log). All 51 `#check` lines
--                  elaborate at this pin, so every name in the five clusters
--                  exists as written; the 50 rg-confirmed rows in the TSV are
--                  now compiler-confirmed too, and
--                  `Nat.pow_dvd_pow_iff_le_right` (the one row grep could not
--                  pin, being toolchain-provided) is confirmed by this round.
--
-- Every `#check` line below has a sibling row in probes/M1-LANE.probe.names.tsv
-- (`name<TAB>confirmed|unverified<TAB>file:line|reason`). Evidence in the TSV
-- is rg-confirmed against the pinned tree
-- proof_verify/.lake/packages/mathlib/Mathlib/; rows whose name is *generated*
-- by `@[to_additive]` cite the multiplicative source line (the additive twin is
-- produced there, so it has no separate declaration site to grep).
--
-- Deliberately absent from this list: every declaration already exported by the
-- DONE chunks (L1…L7, L7-FRAG-01…06, L7-ASM — SIGNATURES.md). Those are
-- `import`ed at the call site, never re-probed. Exclusion count for that
-- reason: 0 (no name in the five clusters below is a DONE-chunk declaration).
--
-- Only names an M1 leaf is expected to need are listed; nothing is padding.
import Mathlib

-- ---------------------------------------------------------------------------
-- (1) binomial expansion and Finset sums — pp. 6–8 expand (a^n + n^s·abck)^n,
--     (b^n + …)^n, (h − …)^n, split off low-order terms, and telescope.
-- ---------------------------------------------------------------------------
#check @add_pow
#check @Nat.choose_succ_succ
#check @Nat.choose_self
#check @Nat.choose_eq_zero_of_lt
#check @Nat.choose_mul
#check @Nat.choose_mul_succ_eq
#check @Nat.cast_choose
#check @Finset.sum_range_succ
#check @Finset.sum_range_succ'
#check @Finset.sum_range_sub
#check @Finset.sum_range_sub'
#check @Finset.sum_congr
#check @Finset.sum_add_distrib
#check @Finset.sum_sub_distrib
#check @Finset.mul_sum
#check @Finset.sum_mul
#check @Finset.sum_mul_sum
#check @Finset.sum_comm

-- ---------------------------------------------------------------------------
-- (2) arithmetic of the congruence modulus n^(k·s+1) (p. 6 (7)–(10)) and the
--     ℤ congruence algebra that carries it.
-- ---------------------------------------------------------------------------
#check @pow_dvd_pow_of_dvd
#check @dvd_pow_self
#check @pow_add
#check @pow_mul
#check @pow_succ
#check @pow_succ'
#check @Nat.pow_dvd_pow_iff_le_right
#check @Int.ModEq.of_dvd
#check @Int.ModEq.mul
#check @Int.ModEq.pow
#check @Int.ModEq.add
#check @Int.ModEq.neg
#check @Int.ModEq.dvd
#check @Int.modEq_iff_dvd
#check @Int.modEq_zero_iff_dvd

-- ---------------------------------------------------------------------------
-- (3) primes / parity for the case `n > 11` (n odd prime, n ≥ 13) and the
--     n-adic binomial facts used with FLT mod n.
-- ---------------------------------------------------------------------------
#check @Nat.Prime.two_le
#check @Nat.Prime.odd_of_ne_two
#check @Nat.Prime.eq_two_or_odd'
#check @Nat.Prime.dvd_choose_self
#check @Int.Prime.dvd_pow'
#check @Int.ModEq.pow_prime_eq_self
#check @Odd.neg_pow
#check @Odd.mul

-- ---------------------------------------------------------------------------
-- (4) the division-free identity trick (ENCODING_MAP §B P14: prove A = B as
--     polynomials in ℤ[X], then evaluate) and the geometric/binomial factor
--     identities of t^n − u^n = (t − u)·Σ t^(n−1−i)u^i (p. 6).
-- ---------------------------------------------------------------------------
#check @Polynomial.eval_finsetSum
#check @Polynomial.X_add_C_ne_zero
#check @geom_sum_mul
#check @mul_geom_sum
#check @geom_sum_eq

-- ---------------------------------------------------------------------------
-- (5) Finset/Nat.choose index algebra for the double/triple sum reindexing of
--     p. 6 R2/R3 (Σ_i Σ_j Σ_l with the l + j ≥ 5 split).
-- ---------------------------------------------------------------------------
#check @Finset.sum_sigma'
#check @Finset.sum_finset_product
#check @Finset.sum_range_add
#check @Finset.sum_sigma
#check @Finset.sum_product

-- 51 names total: cluster (1) 18, (2) 15, (3) 8, (4) 5, (5) 5.
-- The matching rows live in probes/M1-LANE.probe.names.tsv.
