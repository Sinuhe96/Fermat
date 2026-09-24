# Fermat Proof — Lean 4 Formalization Workspace

Formalizing a 33-page elementary proof of Fermat's Last Theorem (custom proof, not Wiles).
Stack: **Lean 4 + Mathlib**, plus Python/sympy for brute-force sanity checks and an
optional local llama.cpp server for proof assistance.

---

## Start here

**First read `AGENTS.md`** — it is the mission statement and the binding
operating rules (we verify the author's proof, we do not write our own).
For a fresh session resume, read `HANDOFF.md` first: it points at
AGENTS.md and summarizes the exact next step.

```bash
docker compose up -d lean          # first run installs the toolchain (~90s), then instant
docker compose exec lean sh /workspace/proof/check_env.sh   # verify everything works
```

Then work in the container:

```bash
docker compose exec lean bash
```

Stop with `docker compose down` (keeps the toolchain volume and build cache).

---

## What's available

Inside the `lean` container:

| Tool | Version | Use |
|---|---|---|
| `lean` | 4.35.0-rc2 | proof checker |
| `lake` | 5.0.0-src | build / package manager |
| `python3` + `sympy` | 1.11.1 | brute-force small cases (n=5,7,11) **before** formalizing |
| `git`, `curl`, `zstd` | — | fetch Mathlib, tools |

The `prover` service (llama.cpp, OpenAI-compatible API on `http://localhost:8080`)
is **not yet usable** — no GGUF model downloaded. See Known Issues.

---

## Layout

| Path | What |
|---|---|
| `PROOF_of_FERMAT.pdf` | source proof (33 A4 pages) |
| `AGENTS.md` | **mission + operating rules — read this first** |
| `HANDOFF.md` | fresh-session resume doc (points to AGENTS.md) |
| `pipeline/` | formalization pipeline (see `pipeline/PIPELINE.md`) |
| `proof/` | **your work goes here** — mounted at `/workspace/proof`, persists on host |
| `proof/check_env.sh` | environment smoke test |
| `models/` | GGUF files for the `prover` service (mounted at `/models`) |
| `Dockerfile` | image definition |
| `entrypoint.sh` | one-time toolchain install into volume |
| `compose.yml` | service definitions |
| `hf_gguf.py` | probe HuggingFace for GGUF availability |
| `or_models.json` | OpenRouter model list |
| `proof_verify/` | scratch/test Lake project |

---

## Rebuilds are cheap — don't fear breaking things

The build is layered stable-to-volatile so any failure resumes from the last good layer:

| Scenario | Time |
|---|---|
| No changes | ~1s |
| Edit `entrypoint.sh` / config | ~5s |
| Delete the image entirely | ~9s |

Design points that make this work:
- Build context is **~250 bytes** — `.dockerignore` keeps the PDF, `proof/`, `models/`,
  and `.buildcache/` out. Those are mounted at runtime, never baked in.
- The **500MB toolchain is not in the image** (~517MB). It installs once into the
  `lean-elan` volume and is skipped afterward.
- Layer cache persists to `.buildcache/` — survives `docker rmi`, restarts, and `down`.

If you change `Dockerfile` layers 1–2 (apt packages, elan bootstrap) it costs more;
layer 3 (config/scripts) is essentially free.

## Where we are

```bash
python pipeline/progress.py --check    # live dashboard + ledger consistency check
```

`pipeline/PROGRESS.md` is the committed snapshot (regenerate with `--write`
when statuses change). Open obstacles live in `pipeline/BLOCKERS.md`;
author-bound math disputes live in `pipeline/05-feedback/`.

---

## Known issues / next steps

1. **No prover model (optional helper, not required).**
   `bartowski/Qwen2.5-Math-7B-Instruct-GGUF` has a confirmed Q4_K_M (~4.7GB);
   Kimina-7B-Distill and Goedel-Prover-SFT ship as safetensors only and need a
   one-time quantize. Note: Docker Desktop is capped at ~8GB RAM, so a 7B model
   and a Mathlib build should not run at the same time.
2. **Pipeline is set up; nothing formalized yet.** Extraction and fidelity gate
   run; `L7-FRAG-01` is the first chunk but its pilot transcription was reset
   (see `HANDOFF.md`). Run the pipeline via `pipeline/PIPELINE.md`: smoke first,
   then extract → fidelity gate → transcribe a chunk → sympy → Lean.
3. **Do the next chunk under AGENTS.md.** The prior pilot attempt treated the
   chunk as "state the conclusion and prove it" — that violated the core rule.
   A chunk must carry the AUTHOR's proof steps and Lean must check that chain.

---

## Useful commands

```bash
docker compose up -d --build lean        # rebuild + start
docker compose logs -f lean              # watch output
docker compose exec lean bash            # shell into container
docker compose exec lean sh /workspace/proof/check_env.sh
docker compose down                      # stop
docker compose build --no-cache lean     # only if cache is genuinely broken
```
