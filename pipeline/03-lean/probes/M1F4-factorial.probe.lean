-- M1F4 S4 probe: the Nat.choose -> falling-factorial bridge for the printed
-- factorial forms of the five X^4 boundary sums (author p. 7, P007-R1 l8-l12):
--   C_i^4 = i(i-1)(i-2)(i-3)/24,  C_{n-1-i}^4 = (n-1-i)(n-2-i)(n-3-i)(n-4-i)/24,
--   and the k = 1,2,3 cases appearing in the mixed pairs.
-- NEVER imported, never in lakefile.toml / Main.lean.
import Mathlib

#check @Nat.choose_eq_descFactorial_div_factorial
#check @Nat.choose_eq_factorial_div_factorial
#check @Nat.descFactorial_eq_choose_mul_factorial
#check @Nat.descFactorial_eq_factorial_mul_choose
#check @Nat.descFactorial_succ
#check @Nat.descFactorial_eq_prod_range
#check @Nat.factorial_succ
#check @Nat.factorial
#check @Nat.choose_one_right
#check @Nat.choose_two_right
#check @Nat.choose_self
#check @Nat.choose_zero_right
#check @Nat.choose_mul_factorial_mul_factorial
#check @Nat.succ_mul_choose_eq
#check @Nat.mul_choose_eq
#check @Nat.choose_succ_succ
#check @Nat.cast_div
#check @Nat.div_mul_cancel
#check @Nat.mul_div_right
#check @Nat.div_eq_of_lt
#check @Nat.cast_mul
#check @Nat.descFactorial_eq_zero_iff_lt
