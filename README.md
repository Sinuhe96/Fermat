# Fermat Proof — Lean 4 verification workspace

This repository formally verifies the existing 33-page proof in
`PROOF_of_FERMAT.pdf`. Lean checks the author's deductive chain; it is not a
workspace for replacing that chain with a different proof.

## Start here

For a fresh session, read `HANDOFF.md` for current status and the exact next
step, then read `AGENTS.md` for the binding rules and mandatory bootstrap.
Before project work, identify the active harness, discover/load relevant skills
through its native mechanism (or read their canonical files directly), start
the persistent container, pass readiness, and validate progress in that order.

The Compose service is named `lean` and runs the project image
`fermat-lean:latest`. The separately installed Docker image
`leanprovercommunity/lean` is not referenced by this repository and can be
ignored.

## Mandatory fresh-session bootstrap

After reading `HANDOFF.md` and `AGENTS.md`, load skills using the active
harness's native mechanism; do not assume Command Code syntax is portable.
Command Code supports `/skills` or `cmdc skills list --debug`; in OMP, use
`skill://<name>` for exposed skills and read repository-local skill files
directly. If a required skill is not exposed by the loader, read its canonical
file directly; if unavailable, report the missing prerequisite before work.
Complete this before running the Docker commands below. Run them from the
Windows host at the repository root:

```powershell
# Skill discovery/loading happens through the agent harness, not this shell.
docker compose up -d lean
docker compose exec -T lean sh /workspace/proof/check_env.sh
docker compose exec -T lean python /workspace/pipeline/progress.py --check
```

The normal readiness check is deliberately compile-free. It validates exact
tool versions, mounts, the persistent Lake project and Mathlib cache, plus a
one-page extraction/rendering smoke test. Use the full check after rebuilding
the image, changing the toolchain, or repairing cache/workspace state:

```powershell
docker compose exec -T lean sh /workspace/proof/check_env.sh --full
```

`--full` additionally compiles a temporary `import Mathlib` file in the Linux
`lake-work` volume.

## Daily workflow

Keep the container running and execute every command in it; do not create and
remove a container per command.

```powershell
# Interactive shell
docker compose exec lean bash

# Compile an authoritative Lean source after copying it internally to lake-work
docker compose exec -T lean sh /workspace/proof/compile_lean.sh L1/Basic.lean

# Search the pinned local Mathlib source before paying for a compile
docker compose exec -T lean rg -n "pow_card_sub_one_eq_one" /workspace/work/testproj/.lake/packages/mathlib/Mathlib

# Render source evidence (one-based page, crop coordinates in PDF points)
docker compose exec -T lean python /workspace/pipeline/01-extract/render_pdf.py `
  /workspace/source/PROOF_of_FERMAT.pdf `
  /workspace/pipeline/01-extract/out `
  --page 2 --dpi 300 --crop 72,90,520,700
```

**Chunk-to-chunk reuse.** A DONE chunk is cited by `import`ing its module,
never by pasting its proof: `import L3.Basic` then `L3.L3_bo_de_3` (see
`pipeline/03-lean/ENCODING_MAP.md` §A "Reusing a DONE chunk").
`compile_lean.sh` syncs the repo-tracked `pipeline/03-lean/lakefile.toml` into
the Lake project and publishes `<module>.olean` as a by-product of every
successful compile, so a producer becomes importable by being compiled once —
no separate `lake build` step. The copies under `pipeline/03-lean/` stay the
source of truth; never edit the Lake-volume copies.

**If `import Lk.Basic` fails**, it means the producer has not been compiled
yet (its olean appears on the first successful compile of that source) or its
`lean_lib` is missing from the repo `lakefile.toml`. Fix that; do **not**
rebuild the environment. `docker compose down -v`, image rebuilds, and
`lake exe cache get` are for a broken toolchain or Mathlib cache
(`check_env.sh` red), never for a wiring problem — they destroy or
re-download state that `check_env.sh` reports as fine.

**Never run `lake`, `lake exe cache get`, or Lean compilation in
`/workspace/proof`, `/workspace/pipeline`, `proof_verify`, or another Windows
bind mount.** Lake work belongs only in `/workspace/work/testproj` on the
Linux `lake-work` volume. `compile_lean.sh` enforces the normal copy-then-build
path.

## Persistent state

| Mount or volume | Purpose |
|---|---|
| `./proof` → `/workspace/proof` | Runtime scripts and temporary probes; no Lake work |
| `./pipeline` → `/workspace/pipeline` | Versioned pipeline, evidence, and authoritative Lean sources |
| `PROOF_of_FERMAT.pdf` → `/workspace/source/...` | Read-only source PDF |
| `lake-work` → `/workspace/work` | Linux-native Lake project, packages, and oleans |
| `lean-elan` → `/elan-home` | Pinned Lean toolchain |
| `lake-cache` → `/root/.cache` | Downloaded Mathlib cache archives |

Ordinary `docker compose down` stops the service while retaining all named
volumes. Do not use `docker compose down -v` unless you intentionally want to
delete the toolchain, Mathlib cache, and Linux Lake workspace.

## Installed toolkit

Inside `fermat-lean:latest`:

| Tool | Purpose |
|---|---|
| Lean 4.35.0-rc2 + Lake 5.0.0 | Formal checking and package management |
| Mathlib v4.35.0-rc2 | Pinned mathematical library in `lake-work` |
| Python with pinned `pypdf`, `PyMuPDF`, and `sympy` | Extraction, rendering, and computational smoke checks |
| `ripgrep` (`rg`) | Fast pin-exact source and lemma search |
| Git, curl, zstd | Dependency and cache support |

The optional `prover` service still requires a compatible GGUF model in
`models/` and must not run alongside a memory-heavy Mathlib compile on the
current Docker Desktop allocation.

## Project navigation

| Path | Purpose |
|---|---|
| `HANDOFF.md` | Live resume point and current verification status |
| `AGENTS.md` | Binding proof-verification workflow |
| `pipeline/PIPELINE.md` | Stage-by-stage pipeline |
| `pipeline/PROGRESS.md` | Generated status snapshot |
| `pipeline/BLOCKERS.md` | Technical obstacle log |
| `pipeline/05-feedback/` | Author-facing mathematical queries |
| `pipeline/03-lean/` | Versioned Lean formalizations |
| `pipeline/01-extract/` | Text extraction and provenance-preserving rendering |
| `docs/IMAGE_BUILD.md` | Image construction, cache layers, and rebuild guidance |

Image building is exceptional maintenance, not the daily workflow. See
`docs/IMAGE_BUILD.md` instead of rebuilding reflexively.
