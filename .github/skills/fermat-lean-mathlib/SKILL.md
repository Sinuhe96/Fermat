---
name: fermat-lean-mathlib
description: Lean 4.35.0-rc2 + Mathlib v4.35.0-rc2 knowledge for THIS repo's mission — verifying the author's FLT proof from PROOF_of_FERMAT.pdf. Use when transcribing author proof steps into .lean, searching for Mathlib lemmas, hitting ZMod/linarith/pow API errors, or compiling in the lean container.
---

# Fermat project — Lean 4 + Mathlib skill

Scope: this repository only (toolchain pin, container layout, pipeline
contracts, project-learned API pitfalls). For the mission rules themselves
see `AGENTS.md` — this skill never overrides them.

## Non-negotiables (from AGENTS.md)

1. Transcribe the AUTHOR's chain from the PDF, in order. Lean checks
   THEIR steps; it is not our job to prove anything ourselves.
2. Sympy smoke BEFORE Lean (`pipeline/04-sympy/`). Counterexample ⇒
   transcription is wrong; fix the chunk, never prove a false lemma.
3. A faithful transcription Lean rejects = finding for the author →
   `pipeline/05-feedback/`. NEVER silently "fix" the author's step.
4. `sorry` = not DONE. A chunk is DONE only when Lean compiles the
   author's full chain AND the ledger is updated.

## Environment (verified in this repo)

| Fact | Value |
|---|---|
| Toolchain | lean 4.35.0-rc2, lake 5.0.0 |
| Mathlib | tag `v4.35.0-rc2`, rev `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Container | `docker compose exec lean …` (service `lean`, image `fermat-lean`) |
| Compile ONLY in | `/workspace/work/testproj` (Linux volume) |
| NEVER compile on | `./proof`, `./proof_verify` — 9p drvfs deadlocks `lake` |
| Mathlib source (in container) | `/workspace/work/testproj/.lake/packages/mathlib/Mathlib/` |
| Mathlib source (on host) | `proof_verify/.lake/packages/mathlib/Mathlib/` (browse/grep only) |
| Python/sympy 1.11.1 | same container, for pre-Lean numeric smoke |

Batch rule: one script per session, exec once. All `#check`s go in ONE
`.lean` file → ONE `lake env lean` round-trip (template:
`proof/NameCheck.lean`). PowerShell cannot run bash-isms — write a script
file instead of heredocs.

## Compile loop

```sh
# host, repo root
docker compose exec lean sh -c 'cd /workspace/work/testproj && lake env lean <file>.lean'
```

- Edit files via normal repo paths (`proof/`, `pipeline/03-lean/`), then
  COPY into `/workspace/work` before compiling (bind mounts are edit-only).
- `import Mathlib` costs ~30–60 s warm; files with `exact?`/`apply?`/
  `rw?`/`simp?` cost much more (each search scans the whole environment —
  a 4-search file measured 413 s under contention). Never run two
  `lake env lean` jobs at once. Batch edits; compile once per iteration.
- Lean reports the FIRST failing author step — that is the signal to
  triage (transcription bug vs. finding for author), not to route around.

## Finding lemmas — full ladder

Detail in `references/search.md`. Summary, cheapest first:

1. **Grep local Mathlib source** (pin-exact, offline): `grep -rn "theorem <hint>" /workspace/work/testproj/.lake/packages/mathlib/Mathlib/`
2. **Loogle JSON**: `curl -s "https://loogle.lean-lang.org/json?q=…"` (verified from container)
3. **In-file tactics**: `exact?` `apply?` `rw?` `simp?` — search the exact compiled env
4. **Natural language**: web UIs leansearch.net / moogle.ai — NOT the
   in-file `#loogle`/`#leansearch` commands, which hang in this
   container (two observed timeouts; `curl` to Loogle works — see
   search.md §4)
5. **Docs** leanprover-community.github.io/mathlib4_docs — may be NEWER than our pin; local source wins ties
6. Guess names via naming conventions → confirm by `#check` batch

## API pitfalls & name-guessing

`references/reference.md`: naming dictionary (`dvd`, `le/lt`, `X_of_Y`,
`X_iff_Y`), tactics table scoped to this project's math (ℤ/ℕ/`ZMod`),
ZMod rules that already cost compile time, error→fix table.

FIRST READ for encoding: `pipeline/03-lean/MATHLIB_API_LESSONS.md` —
the repo's live ledger of hard-won API facts. Append new lessons there
after every session that pays for one.

## Trust checks

```lean
#print axioms my_thm   -- only Classical.choice, propext, quot.sound allowed
```

Compiles ≠ done: no `sorry`, no custom axioms, ledger updated
(`pipeline/02-chunks/status.tsv` + chunk YAML + regenerated `PROGRESS.md`).
