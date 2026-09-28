/-
`B-01` probe 2 — the exact signatures the second equality of B.2 needs.

Round 17/18 both died on arithmetic, not mathematics: the first attempt used
`omega` on truncated-subtraction monotonicity (`y ≥ m - k ⊢ m - 1 - y < k`),
which `omega` cannot do here, and the second assumed `Finset.sum_subset`'s
vanishing hypothesis was `∀ x ∈ t, x ∉ s` — the elaboration error says it is
`∀ x ∈ s, x ∉ t`, i.e. the binders come back in the other order. One probe
round answers every remaining shape question at once (Mathlib's oleans are
cached, so this costs ~8 s, not the 250-400 s a full proof round costs).
-/
import Mathlib

#print Finset.sum_subset
#check @Finset.sum_subset
#check @Finset.sum_range_add
#check @Finset.sum_union
#check @Finset.sum_eq_zero
#check @Finset.sum_range_eq_add_sum_Ico
#check @tsub_lt_iff_right
#check @tsub_add_cancel_of_le
#check @Nat.sub_sub
#check @Nat.succ_le_iff
#check @Nat.sub_le
#check @Nat.le_of_not_lt
#check @Nat.add_le_add_right
