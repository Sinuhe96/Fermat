-- Probe for chunk L7-FRAG-01 (bo de 7, its L5-side toolkit) -- reconstructed
-- 2026-09-27 from `03-lean/L7-FRAG-01_compile_20260926.log` and the 2026-09-26
-- session entry in `MATHLIB_API_LESSONS.md` (the original probe source was
-- deleted before it could be archived).
--
-- chunk ids:       L7-FRAG-01
-- date:            2026-09-28 (reconstruction re-run; the list itself was
--                  first written 2026-09-26)
-- toolchain:       lean 4.35.0-rc2 / lake 5.0.0
-- mathlib rev:     v4.35.0-rc2 (065356127b1dc001f66b7283ce0ce2c4055aa55)
-- run command:     sh /workspace/proof/compile_lean.sh probes/L7-FRAG-01.probe.lean
-- log:             probes/L7-FRAG-01.probe.log
-- status:          VERIFIED (EXIT=0, no error lines, all 21 names resolved)
--
-- Note: `ZMod.intCast_zmod_eq_zero_iff_dvd` takes explicit arguments, so
-- `#check` prints it without a leading `@` (log line 20).
import Mathlib
import L5.Basic

#check @pow_eq_zero_iff
#check @dvd_pow_self
#check @sub_eq_zero
#check @neg_inj
#check @add_eq_zero_iff_eq_neg
#check @mul_eq_zero
#check @mul_eq_zero_iff_right
#check @pow_ne_zero
#check @mul_pow
#check @Odd.neg_pow
#check @Nat.Prime.odd_of_ne_two
#check @Nat.Prime.eq_two_or_odd'
#check @Int.Prime.dvd_pow'
#check @Int.modEq_zero_iff_dvd
#check @Int.modEq_iff_dvd
#check @Int.natCast_dvd_natCast
#check @ZMod.intCast_zmod_eq_zero_iff_dvd
#check @ZMod.pow_card_sub_one_eq_one
#check @ZMod.pow_card
#check @L5.L5_zmod_intCast_eq_zero_iff
#check @L5.L5_gcd_eq_one_of_not_dvd
