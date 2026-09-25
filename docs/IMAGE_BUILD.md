# Building the `fermat-lean` image

Daily work should start the existing persistent service with
`docker compose up -d lean`. This document is only for changing or repairing
the project image.

## Which image the project uses

`compose.yml` builds and runs `fermat-lean:latest` from the root `Dockerfile`.
It starts from Debian Bookworm Slim, installs the project toolkit, and uses
Elan to install the pinned Lean toolchain into the persistent `lean-elan`
volume on first startup.

The locally present `leanprovercommunity/lean` image is not a base image,
Compose dependency, or runtime fallback for this repository. Docker Desktop
may list it, but no project instruction should invoke it.

## Build and verify

```powershell
docker compose build lean
docker compose up -d lean
docker compose exec -T lean sh /workspace/proof/check_env.sh --full
```

`docker compose up -d --build lean` is a convenient equivalent when changing
the Dockerfile or pinned Python requirements.

Use a no-cache build only after evidence that the image layer cache itself is
corrupt or masking a Dockerfile problem:

```powershell
docker compose build --no-cache lean
```

A no-cache image build does not reset `lean-elan`, `lake-cache`, or
`lake-work`. Conversely, rebuilding the image does not repair bad contents in
those runtime volumes.

## Layer and cache design

The image is ordered from stable to volatile:

1. Debian packages, `ripgrep`, and Python virtual-environment support.
2. Exact Python dependencies from `requirements-container.txt`.
3. Elan bootstrap without a Lean toolchain.
4. The runtime entrypoint.

`.dockerignore` allowlists only `Dockerfile`, `entrypoint.sh`, and
`requirements-container.txt`, so the PDF, source tree, generated evidence,
models, and caches are never sent to the image builder.

Four separate persistence mechanisms matter:

| State | Location | Lost when |
|---|---|---|
| Docker image layers | Docker/BuildKit plus `.buildcache` | Builder cache is pruned or bypassed |
| Lean toolchain | `lean-elan` volume | That volume is removed |
| Mathlib download cache | `lake-cache` volume | That volume is removed |
| Lake project, packages, and oleans | `lake-work` volume | That volume is removed |

Ordinary `docker compose down` retains all named volumes. Avoid `down -v`
unless a deliberate full reset is required.

## Rebuild triggers

Rebuild when changing:

- `Dockerfile`;
- `entrypoint.sh`;
- `requirements-container.txt`.

Do not rebuild for changes under `pipeline/`, `proof/`, the source PDF, or
Lean proof files; those are runtime mounts and the Linux work volume.

## Essential toolkit now installed

- `ripgrep` for fast offline search in the exact pinned Mathlib source;
- exact `pypdf` and `PyMuPDF` versions for dual extraction and deterministic
  page/crop rendering;
- exact `sympy` for bounded computational checks;
- a hard-failing fast readiness check and an explicit full Mathlib compile
  mode.

The following are intentionally deferred:

- OCR: potentially useful for ambiguous regions, but visual PDF confirmation
  remains authoritative and the current PDF already has a text layer;
- local LLM reviewer: useful only as an independent evidence-packet reviewer,
  not as a proof authority, and it competes with Lean for limited RAM;
- CI/editor integration: valuable after the tracked Lake project is made fully
  reproducible;
- canonical Lake module wiring: the known volume-only package configuration
  remains a separate structural change, documented in
  `pipeline/03-lean/ENCODING_MAP.md`.

## Diagnostics

```powershell
# Effective Compose model
docker compose config

# Service state
docker compose ps

# Image identity
docker image inspect fermat-lean:latest

# Fast check (no Lean compile)
docker compose exec -T lean sh /workspace/proof/check_env.sh

# Full check (includes import Mathlib compile)
docker compose exec -T lean sh /workspace/proof/check_env.sh --full
```

Diagnose image layers, `lean-elan`, `lake-cache`, and `lake-work` separately;
do not erase all state to solve a failure in only one layer.
