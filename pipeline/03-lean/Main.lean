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

-- Parked scratch module for the blocked chunk L7-FRAG-01 (2 sorries, author
-- query Q-001 open): kept out of the verified set above and never cited.
import Pilot.Basic
