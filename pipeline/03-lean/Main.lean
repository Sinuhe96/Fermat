-- Module root: wires every chunk root that must compile.
--
-- Importability requires the producing chunk to have been compiled once
-- through `proof/compile_lean.sh`, which publishes its olean (see
-- ENCODING_MAP §A "Reusing a DONE chunk"). Verified chunk libraries:
import Common.Basic
import L1.Basic
import L2.Basic
import L3.Basic
import L4.Basic
import L5.Basic
import L6.Basic
-- L7 carries bổ đề 7's non-divisibility conclusion (S0–S6, all S1; S5c is an
-- F3 fill-in — the printed reductio re-instantiated at (X,Y,Z) = (−b,a,c)).
import L7.Basic
-- L7F2…L7F6 are bổ đề 7's remaining conclusion groups, one chunk each
-- (displays (a)–(d), (19)/(20), (18)/(22'), n ≡ 1 (mod 6), (21)/(22));
-- L7ASM is their section assembly and exposes `L7_bo_de_7`, the lemma's
-- complete conclusion list — the entry point the main proof cites.
import L7F2.Basic
import L7F3.Basic
import L7F4.Basic
import L7F5.Basic
import L7F6.Basic
import L7ASM.Basic
