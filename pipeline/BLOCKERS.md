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

## B-001 Mathlib olean cache does not unpack [OPEN]

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
