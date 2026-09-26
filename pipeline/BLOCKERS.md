# Obstacles (BLOCKERS.md)

One section per obstacle. Newest on top. An obstacle is OPEN until its
resolution is verified by the check named in the entry — not when a
workaround merely looks plausible.

Format per entry:
- `## B-NNN title [OPEN|RESOLVED]` — status in the heading, machine-read by `progress.py`.
- Impact / Unblocks / First seen / Owner / Workaround / Resolution.

When an obstacle is technical (toolchain, cache, RAM) it stays here.
When verification of a chunk FAILS on the math, open an author query in
`05-feedback/queries/` instead and link it from the chunk — do not
clutter this log with mathematical disputes.

---

## B-002 Chunk-import wiring untracked, package file unsynced, producers never built [RESOLVED]

- Impact: `import Lk.Basic` from a consumer chunk could not resolve. The
  `lean_lib` wiring existed only in an untracked `pipeline/03-lean/lakefile.toml`,
  `proof/compile_lean.sh` never copied the package file into
  `/workspace/work/testproj`, and `.lake/build/lib/lean/L3/` was an empty
  directory (no producer olean had ever been produced). The first consumer —
  L4-01 (bổ đề 4 cites bổ đề 3) — would have paid a full 150–350 s round-trip
  to discover the import failure.
- Root cause: the copy-then-compile harness handled `.lean` sources only, and
  `lake env lean <file>` emits no olean, so no chunk was ever importable. The
  volume's `lakefile.toml` and the (untracked) repo copy were already two
  unsynced sources of truth; ENCODING_MAP §A had flagged the volume-only copy
  as a known gap.
- First seen: 2026-09-26 (L3-01 close-out; diagnosed while checking what the
  L4 session needed).
- Fix: `pipeline/03-lean/lakefile.toml` is tracked, with `[[lean_lib]]`
  entries (explicit `roots`) for `Common`, `L1`, `L2`, `L3`;
  `proof/compile_lean.sh` now syncs that file into the package and compiles
  with `lean -o <package>/.lake/build/lib/lean/<relative>.olean`, after an
  `rm -f` of the previous olean so a failed compile cannot publish a stale
  artifact.
- Resolution check: verified 2026-09-26 — (a) `lean -o` on a module with a
  type error and on one with a failed tactic exits 1 and writes **no** olean;
  (b) `lean -o` on a trivial module plus `import` of it from a second file
  works (olean written, 4 s, no Mathlib import); (c) a real
  `compile_lean.sh L3/Basic.lean` round leaves
  `.lake/build/lib/lean/L3/Basic.olean` in place (round 12 of
  `03-lean/L3-01_compile_20260926.log`); (d) independently corroborated by
  the other session: `lake build L3` (01:20) published
  `L3/{Basic.olean, Basic.ilean, Basic.trace}` plus `.lake/build/ir/L3/`, so
  the declared library builds through lake's own route too.

## B-003 `Main.lean` aggregator listed a sorry-carrying scratch module [RESOLVED]

- Impact: the aggregate root cannot serve as a build-all gate.
  `03-lean/Pilot/Basic.lean` is the parked L7-FRAG-01 scratch file and still
  contains 2 `sorry`s; nothing builds `Main.lean` (Lake's `defaultTargets` is
  `Testproj`), so the defect stays latent.
- Unblocks: any future "compile everything" gate, and the resolution of
  L7-FRAG-01 / Q-001, which decides whether `Pilot/Basic.lean` is deleted or
  superseded.
- First seen: 2026-09-26 (L3-01 close-out).
- Workaround applied: `Main.lean` now lists the verified chunk libraries
  (`Common`, `L1`, `L2`, `L3`) as its verified set and marks the
  `import Pilot.Basic` line as parked with a comment tying it to Q-001;
  `ENCODING_MAP.md` §A records the same.
- Resolution check: either `grep -c sorry 03-lean/Pilot/Basic.lean` returns 0,
  or the `import Pilot.Basic` line is gone from `Main.lean`.
- Measured 2026-09-26 (L6-01 close-out), so the L7 lane does not re-pay it:
  `lake build Common L1 L2` in `/workspace/work/testproj` → EXIT 0 (8936
  jobs). Those three were the last libs whose oleans predated B-002's `lean -o`
  publishing (L3–L6 got theirs in their own sessions), so the *verified* set
  `Common, L1..L6` is now fully importable. `lake env lean Main.lean` therefore
  gets past every verified lib and stops at exactly one line:
  `unknown module prefix 'Pilot'` (Pilot is not a `lean_lib` and its source was
  never copied into the Lake project — by design, it is the parked scratch
  copy). So the whole remaining defect is that single import line, and the
  recipe for the L7 session is: settle Q-001 → delete `Pilot/Basic.lean` (or
  supersede it with `03-lean/L7/Basic.lean` as a declared `lean_lib`) → drop
  the `import Pilot.Basic` line → `lake build L7` (publishes the olean) →
  `lake env lean Main.lean` EXIT 0, which then makes the aggregate a
  sorry-free "everything typechecks" gate.
  Note `Common/Basic.lean` is an empty scaffold (2 comment lines, no
  declarations) imported only by `Main.lean`; it is the designated home for
  chunk-shared helpers and needs no change for bổ đề 7.
- Resolution (2026-09-26, `L7-FRAG-01` lane restart): the chunk's lane was
  redone one-step-per-compile as `03-lean/L7/Basic.lean` (S0–S5 all S1,
  `sorry`-free, permitted axioms only) and declared as `lean_lib L7` with
  `roots = ["L7.Basic"]`; `Main.lean` now imports `L7.Basic` and no longer
  mentions `Pilot`, whose `[[lean_lib]]` entry is gone from `lakefile.toml`.
  `Pilot/Basic.lean` stays in the tree, marked "FROZEN PRE-RESTART EXHIBIT", as
  the Lean exhibit cited by author query Q-001; nothing imports it.
- Resolution check: PASSED 2026-09-26 — (a) the `import Pilot.Basic` line is
  gone from `Main.lean` (only `import L7.Basic` was added to the verified set
  `Common`, `L1`–`L6`); (b) `sh proof/compile_lean.sh Main.lean` → EXIT 0
  (373 s), i.e. the aggregate root compiles every chunk including L7 — the
  `sorry`-free "everything typechecks" gate this entry asked for;
  (c) `python pipeline/progress.py --check` exit 0.

## B-001 Mathlib olean cache does not unpack [RESOLVED]

- Impact: `03-lean/` files could not `import Mathlib`.
- Root cause (verified by diagnosis, not the original guess): TWO stacked
  issues. (1) The "410 oleans" were only Batteries/Cache-exe artifacts in
  the Windows bind-mounted `proof_verify/.lake` — `cache get` had never
  completed there. (2) Running `cache get` on the 9p drvfs bind mount
  deadlocked the fetch process in `D` state (`p9_client_rpc`), so it could
  never complete there — the original "wiped cache dir" theory was wrong.
- Fix: fresh `lake new testproj math` in `/workspace/work` (Linux
  `lake-work` volume, ext4) + `lake exe cache get` (8915 files, ~446MB
  ltar in `lake-cache` volume) + `lake exe cache unpack` (8936 oleans).
  `Mathlib.olean` verified at
  `testproj/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`.
  `import Mathlib` compiles (`CheckMathlib.lean` → `Nat.Prime` check, EXIT 0).
- Rule going forward: Lake work happens ONLY in `/workspace/work`
  (Linux volume). `proof_verify/` on Windows is edit-only, never `lake`.
  See compose.yml NOTE.
- Resolution check: PASSED — `find` returns `Mathlib.olean` AND
  `lake env lean` compiles a file containing `import Mathlib`.

<details><summary>Original report (superseded diagnosis)</summary>

- Impact: `03-lean/` files cannot `import Mathlib`; only statement-shape
  scaffolds compile. All Lean formalization is gated on this.
- Unblocks: every chunk's DONE criterion 1 (`lake env lean` with no sorry).
- First seen: workspace setup (see README "Known issues").
- Symptom: `lake exe cache get` exits 0 but no `Mathlib.olean` appears
  (410 dep oleans only, no Mathlib root olean).
- Suspected cause: each `docker run --rm` wipes the cache dir, so the
  download never persists; needs one persistent container run with the
  `lean-elan` volume mounted (compose already declares it).
- Workaround: none yet — building Mathlib from source (~hours, risky at
  6GB RAM cap) is the fallback.
- Resolution check: `find .lake -name "Mathlib.olean"` returns a file AND
  `lake env lean` compiles a file containing `import Mathlib`.

</details>
