-- Probe for chunks L7-FRAG-02 … L7-FRAG-06 (bổ đề 7's remaining conclusion groups).
--
-- chunk ids:       L7-FRAG-02 (toolkit (a)-(d)) … L7-FRAG-06 ((21)+(22)),
--                  consumed by the section assembly L7-ASM
-- date:            2026-09-27
-- toolchain:       lean 4.35.0-rc2 / lake 5.0.0
-- mathlib rev:     v4.35.0-rc2 (065356127b1dc001f66b7283ce0ce2c4055aa55)
-- run command:     sh /workspace/proof/compile_lean.sh probes/L7-FRAG-02.probe.lean
-- log:             probes/L7-FRAG-02.probe.log
-- status:          VERIFIED (see the log)
--
-- Consume rule (ENCODING_MAP §A "Probe archive"): read your dependencies'
-- probes first, `rg`-check each reused name free on the pinned tree, extend —
-- never fork — and re-run when the rev, the log, or a name is missing.
--
-- Names reused from L5 (bổ đề 5) are cited by the probes of L7-FRAG-01 as well;
-- they are re-checked here because this probe file, not the older one, is the
-- one whose log backs the declarations written in this session.
import Mathlib
import L5.Basic

-- Int.ModEq combinators (the mod-n / mod-n² algebra of the whole session)
#check @Int.ModEq.mul
#check @Int.ModEq.add
#check @Int.ModEq.sub
#check @Int.ModEq.neg
#check @Int.ModEq.pow
#check @Int.ModEq.add_left
#check @Int.ModEq.add_right
#check @Int.ModEq.mul_left
#check @Int.ModEq.mul_right
#check @Int.ModEq.refl
#check @Int.ModEq.trans
#check @Int.ModEq.symm
#check @Int.ModEq.dvd
#check @Int.ModEq.of_dvd
#check @Int.modEq_iff_dvd
#check @Int.modEq_zero_iff_dvd
#check @Int.ModEq.pow_prime_eq_self
#check @Int.ModEq.pow_card_sub_one_eq_one
#check @Int.ModEq.of_dvd
#check @Int.natCast_dvd_natCast
#check @Int.natCast_dvd
#check @Int.dvd_natCast

-- ℤ divisibility toolkit
#check @dvd_pow_self
#check @dvd_mul_of_dvd_right
#check @dvd_mul_of_dvd_left
#check @dvd_sub
#check @dvd_add
#check @dvd_neg
#check @neg_dvd
#check @dvd_trans
#check @Int.Prime.dvd_mul'
#check @Int.Prime.dvd_pow'
#check @Int.pow_dvd_pow_iff
#check @Int.isCoprime_iff_gcd_eq_one
#check @Int.isCoprime_iff_nat_coprime
#check @IsCoprime.dvd_of_dvd_mul_left
#check @IsCoprime.dvd_of_dvd_mul_right
#check @IsCoprime.pow

-- exponent identities (ℕ side)
#check @pow_mul
#check @pow_add
#check @pow_succ
#check @pow_succ'
#check @pow_two
#check @mul_pow
#check @Nat.mul_sub_left_distrib
#check @Nat.sub_add_cancel
#check @Nat.sub_one_add_one_eq_of_pos
#check @Nat.mul_add
#check @Nat.add_mul
#check @Nat.mul_sub_right_distrib
#check @Nat.sub_mul
#check @Nat.sub_eq_iff_eq_add
#check @Nat.Coprime.dvd_of_dvd_mul_right
#check @Nat.Prime.coprime_iff_not_dvd
#check @Nat.Prime.dvd_of_dvd_pow
#check @Nat.le_of_dvd
#check @Nat.mul_right_cancel

-- parity / primality bridges used by the n ≡ 1 (mod 6) chunk
#check @Odd.neg_pow
#check @Odd.mul
#check @Odd.pow
#check @Odd.neg_one_pow
#check @Nat.Prime.odd_of_ne_two
#check @Nat.Prime.eq_two_or_odd
#check @Nat.Prime.eq_two_or_odd'
#check @Nat.Prime.two_le
#check @Nat.Prime.one_lt
#check @Nat.Prime.pos
#check @Nat.Prime.ne_one
#check @Nat.Prime.ne_zero
#check @Nat.odd_iff
#check @Nat.even_iff
#check @Nat.dvd_prime
#check @Nat.Prime.eq_one_or_self_of_dvd
#check @Nat.Prime.dvd_iff_eq
#check @Nat.Prime.not_dvd_one
#check @Nat.dvd_of_mod_eq_zero
#check @Nat.mod_eq_of_lt
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @Nat.dvd_iff_mod_eq_zero

-- L5 surface reused by these chunks (bổ đề 5c/5đ and the c)-branch pieces)
#check @L5.L5_step_S12
#check @L5.L5_step_S15
#check @L5.L5_step_S16
#check @L5.L5_step_S17
#check @L5.L5_step_S18
#check @L5.L5_bo_de_5
#check @L5.L5_gcd_eq_one_of_not_dvd
#check @L5.L5_step_S2
#check @L5.L5_step_S4
#check @L5.A
#check @L5.B'
