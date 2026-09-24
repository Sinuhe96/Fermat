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
