-- M1F4 re-indexing probe (step S2, second half).
-- NEVER imported, never in lakefile.toml / Main.lean. One `#check` batch pins the
-- names for the (j,l,i) re-indexing of the printed `l+j ≤ 4` boundary sums.
-- A name that does not exist prints "unknown identifier" — that is the answer we
-- want, and it is cheaper here than in a proof round.
import Mathlib

-- Flattening nested sums to a single Finset of pairs/triples:
#check @Finset.sigma
#check @Finset.sum_sigma
#check @Finset.sum_sigma'
#check @Finset.mem_sigma
-- Reindexing a sum along a bijection:
#check @Finset.sum_bij
#check @Finset.sum_bij'
#check @Finset.sum_nbij
#check @Finset.sum_nbij'
#check @Finset.sum_equiv
-- Splitting / filtering:
#check @Finset.sum_filter
#check @Finset.sum_filter_of_ne
#check @Finset.sum_ite
#check @Finset.sum_ite_eq
#check @Finset.sum_ite_eq'
#check @Finset.sum_boole
#check @Finset.sum_comm
#check @Finset.sum_product
#check @Finset.sum_subset
#check @Finset.sum_subset_zero_on_sdiff
#check @Finset.sum_congr
-- Range/Ico arithmetic:
#check @Finset.range_eq_Ico
#check @Finset.sum_Ico_eq_sum_range
#check @Finset.sum_range_succ
#check @Finset.sum_Ico_succ_top
#check @Finset.sum_range_add_sum_Ico
#check @Finset.mem_Ico
#check @Finset.mem_range
-- Nat side conditions the reindexing needs:
#check @Nat.lt_iff_add_one_le
#check @Nat.add_lt_iff_lt_sub
#check @Nat.le_sub_iff_add_le
#check @Nat.sub_le_sub_left
#check @Nat.lt_sub_iff_add_lt
#check @Nat.sub_lt_sub_left
