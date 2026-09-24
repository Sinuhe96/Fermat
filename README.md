# Fermat Proof — Lean 4 Formalization Workspace

Formalizing a 33-page elementary proof of Fermat's Last Theorem (custom proof, not Wiles).
Stack: **Lean 4 + Mathlib**, plus Python/sympy for brute-force sanity checks and an
optional local llama.cpp server for proof assistance.

---

## Start here

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
| `PROOF_of_ FERMAT.pdf` | source proof (33 A4 pages) |
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

---

## Known issues / next steps

1. **Mathlib olean cache does not unpack.** `lake exe cache get` exits 0 but leaves no
   `Mathlib.olean`. Until fixed, building Mathlib from source is the alternative.
2. **No prover model.** `bartowski/Qwen2.5-Math-7B-Instruct-GGUF` has confirmed Q4_K_M
   (~4.7GB). Kimina-7B-Distill and Goedel-Prover-SFT ship as safetensors only and need a
   one-time quantize. Note: Docker Desktop is capped at ~8GB RAM, so a 7B model and a
   Mathlib build should not run at the same time.
3. **Nothing formalized yet.** Next real step is piloting the first lemma from the PDF
   (see the image lemma: prime `n>3`, `n ∤ abc`, `a^n+b^n-c^n ≡ 0 [n²]` ⟹
   `(a^n-b^n)(c^n+a^n)(c^n+b^n) ≢ 0 [n]`) — brute-force it for n=5,7,11 in sympy,
   then write the Lean statement.

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
