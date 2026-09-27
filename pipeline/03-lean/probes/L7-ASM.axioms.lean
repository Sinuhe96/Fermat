-- Final gate for the bổ đề 7 lane (chunks L7-FRAG-02 … L7-FRAG-06 + L7-ASM):
-- `#print axioms` on the section assembly and on each leaf's key declaration,
-- plus a `sorry`-free assertion by construction (the file compiles or it does
-- not). Not imported by anything; compile with
--   sh /workspace/proof/compile_lean.sh probes/L7-ASM.axioms.lean
import Mathlib
import L7.Basic
import L7F2.Basic
import L7F3.Basic
import L7F4.Basic
import L7F5.Basic
import L7F6.Basic
import L7ASM.Basic

#print axioms L7.L7_bo_de_7
#print axioms L7.L7F2_step_S0
#print axioms L7.L7F2_step_S1
#print axioms L7.L7F2_step_S2
#print axioms L7.L7F2_step_S3
#print axioms L7.L7F2_step_S4
#print axioms L7.L7F3_five_c
#print axioms L7.L7F3_five_d_cube
#print axioms L7.L7F3_step_S5
#print axioms L7.L7F3_step_S6
#print axioms L7.L7F3_step_S7
#print axioms L7.L7F3_step_S8_S9
#print axioms L7.L7F3_chain_ab
#print axioms L7.L7F3_step_S10
#print axioms L7.L7F3_step_S11
#print axioms L7.L7F4_sum_chain
#print axioms L7.L7F4_step_S12
#print axioms L7.L7F4_step_S13
#print axioms L7.L7F4_step_S14
#print axioms L7.L7F5_step_S15
#print axioms L7.L7F5_step_S16
#print axioms L7.L7F5_step_S17
#print axioms L7.L7F6_step_S18
#print axioms L7.L7F6_step_S19
#print axioms L7.L7F6_step_S20
#print axioms L7.L7F6_step_S21
