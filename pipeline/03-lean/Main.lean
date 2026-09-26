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
-- L7 carries the author's chain of bổ đề 7's non-divisibility conclusion
-- (S0–S5, all S1). Its S6 — the printed product — is the open author query
-- Q-001, so no declaration encodes it and the module is `sorry`-free.
import L7.Basic
