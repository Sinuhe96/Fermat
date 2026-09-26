# AGENTS.md — operating rules for this repository

These rules are binding on any agent working here. They exist to prevent
repeated, expensive mistakes. When in doubt, follow this file over
general coding habits.

## Mandatory fresh-session bootstrap

Before any project work, every new agent session must complete this sequence
in order. Do not inspect a chunk, edit files, search Mathlib, or run Lake first.

1. Read `HANDOFF.md` for live status and the exact next step, then read this
   `AGENTS.md` in full. `README.md` is the runtime command reference.
2. Identify the active agent harness and use its native skill discovery/loading
   mechanism. Command Code supports `/skills` or `cmdc skills list --debug`;
   OMP exposes skills through `skill://<name>` resources, and repository-local
   skill files can be read directly. Do not run another harness's commands.
   If a relevant skill is not exposed, read its canonical file directly; if
   neither the harness nor repository provides it, report the missing
   prerequisite before work. Load every skill relevant to the task. Normal
   proof work requires `lean4` and the Fermat overlay before any Lean/Lake
   action.
3. Start the persistent runtime: `docker compose up -d lean`.
4. Run the hard readiness gate:
   `docker compose exec -T lean sh /workspace/proof/check_env.sh`.
   Use `--full` after image, toolchain, cache, or Lake-workspace changes.
5. Verify project state with
   `docker compose exec -T lean python /workspace/pipeline/progress.py --check`.
6. Only after steps 1–5 are green, open the current chunk/source evidence and
   begin the task. If any gate fails, fix the skills/infrastructure/tracking
   problem before touching the mathematics.

## Mission

We are building a **formalized verification** of an existing proof of
Fermat's Last Theorem found in `PROOF_of_FERMAT.pdf` (Vietnamese, 33
pages). The proof is complete and already written. We are NOT proving the
theorem ourselves, and we are NOT writing a new proof.

## THE core rule: verify the author's proof, not our own

The proof lives in the PDF. We transcribe the AUTHOR's deductive chain
into Lean, and Lean verifies whether THAT chain is correct.

- **Transcribe the PDF's proof verbatim** — every hypothesis, every
  substitution, every mod reduction, in the author's order.
- **Re-encode that same chain in Lean** — each author step becomes a Lean
  step mirroring their reasoning (same intermediate claims, same order).
- **Lean is the checker.** It certifies the author's chain of inferences,
  or exposes the first step that fails.
- A Lean rejection of a faithfully-transcribed step is a REAL FINDING
  about the proof (a gap or an error). File it to the author per
  `pipeline/05-feedback/README.md` — do not work around it.

### What we must NEVER do

- Do NOT invent, derive, or substitute our own proof. If we prove a
  reformulation, we have NOT verified the author's work — we have written
  a different, weaker artifact.
- Do NOT silently "fix" an author's step that Lean rejects. If our
  transcription is faithful and Lean rejects it, that is a finding for the
  author. Only "fix" when our OWN transcription is wrong.
- Do NOT treat a conclusion statement as the chunk. The chunk must carry
  the author's actual proof steps, not just the headline result.

### The transcription-speed rule (why we stay in this lane)

Transcription is cheap: decode the author's steps from the relevant PDF
renders and encode each as a Lean step. There is nothing to derive. If a
task starts to feel like proof research, stop: re-read the PDF proof and
return to the first author step not yet represented in Lean.

Mathlib usually contains the elementary mathematics needed here, but its
names, types, hypotheses, and normal forms may differ from the paper. It is
legitimate to search for the exact Mathlib API, prove type/cast bridges, and
make implicit side conditions explicit. It is not legitimate to search for
a different mathematical route to the conclusion.

## Project skill map — discover before acting

Skill discovery and activation are harness-specific. Use the active harness's
native mechanism: Command Code supports `/skills` or `cmdc skills list
--debug`; OMP exposes skills through `skill://<name>` resources. If a
particular skill is not exposed, read its canonical file in this map directly;
if the required source is unavailable, report the blocker before work. Skills
are generic playbooks: **this AGENTS.md and the PDF verification rules
override any conflicting skill instruction.**

| Skill | Use in this project | Activation and boundary |
|---|---|---|
| [`lean4`](.commandcode/skills/lean4/SKILL.md) | **Primary general Lean aid.** Use for editing/debugging `.lean`, diagnostics, Mathlib lemma/API search, cast/typeclass errors, `sorry`/axiom review, or Lean/Lake failures. Its LSP/search/error references are useful, but all compilation still uses this repo's container and Linux-volume workflow. | Load through the active harness; if this skill is not exposed, read the linked file directly. Do not use its autoformalize/autoprove/final-theorem workflows to invent or replace the author's chain. |
| [`lean-proof`](.commandcode/skills/lean-proof/SKILL.md) | **Narrow troubleshooting reference only.** Its syntax→type→goal→linter error priority and dependent-rewrite pattern can help on the *current author step*. | Load only for a local proof-state or dependent-rewrite problem, using the active harness or by reading the linked file directly if it is not exposed. Ignore its "hardest case first", "go directly to target theorem", proof-minimization, and strategic-`sorry` advice here: those conflict with strict PDF/source order and S1 completion. Never let it choose step order. |
| [`mathlib-build`](.commandcode/skills/mathlib-build/SKILL.md) | **Exceptional environment maintenance.** Use when the pinned Mathlib cache is missing/corrupt, when changing Mathlib itself, or when diagnosing a real Lake/olean build failure. | Load only after the fast/full environment check identifies a cache/build problem, using the active harness or by reading the linked file directly if it is not exposed. Run its Lake commands only in `/workspace/work/testproj`; never force cache download or build all Mathlib during normal proof work. Repository cache instructions and `docs/IMAGE_BUILD.md` take precedence. |
| [`lean4-setup`](.commandcode/skills/lean4-setup/SKILL.md) | **Normally not applicable.** It builds and links a source clone of the Lean compiler (`leanprover/lean4`); this project consumes a pinned release through Elan and Docker. | Load only if explicitly working on or repairing a Lean compiler source clone outside the normal Fermat workspace, using the active harness or by reading the linked file directly if it is not exposed. Do not run its CMake/Make/toolchain-link commands for routine setup, image rebuilds, or proof verification. |

The separate repository-specific skill
`.github/skills/fermat-lean-mathlib/SKILL.md` is the authoritative overlay
for this exact toolchain pin, container layout, Mathlib API lessons, and
compile/search loop. Read it from the repository in every harness; it does
not depend on harness auto-discovery.

## Required preparation for every Lean session

**MUST load the Lean skills before any Lean work.** Use the active harness's
native loader when available; otherwise read the canonical skill file directly.
The slash-command examples above are Command Code syntax, not universal syntax.
Prepare in this order:

1. Load `lean4` through the active harness, or read
   `.commandcode/skills/lean4/SKILL.md` directly.
2. Read `.github/skills/fermat-lean-mathlib/SKILL.md` in full.
3. Read its `references/search.md` and `references/reference.md` in full.
4. Read `pipeline/03-lean/MATHLIB_API_LESSONS.md`.
5. Read `pipeline/03-lean/ENCODING_MAP.md`.

Load `lean-proof` through the active harness, or read its linked file directly,
only for a local proof-state or dependent-rewrite blocker. Never edit a `.lean`
file, run `lake`, or search for a lemma before completing the required gate.
The `lean4` skill carries the toolchain pin, the container compile loop, the
9p-bind-mount deadlock rule, the lemma-search ladder and the error→fix
table; an agent that skips it reliably reproduces failures this repo has
already paid for (running `lake` inside the Windows bind mount, wasting
multi-minute compile round-trips on wrong guesses, wrong `ZMod`/`Int`/
`Int.gcd` API). Do not re-derive what is already written down.

Then, before editing a Lean proof:

1. Confirm the bootstrap readiness and progress gates are green and identify
   the one current chunk from `HANDOFF.md`.
2. Read the chunk YAML, its rendered PDF source pages, and its dependencies.
3. Bind the chunk to its extraction run: run
   `pipeline/01-extract/fidelity_check.py` (exit 0 required) and fill the
   chunk's evidence fields (`source_pdf_sha`, `extract_run_sha`, `fidelity`,
   `renders`, `lean_decls`) per `02-chunks/schema.md`. `progress.py --check`
   machine-verifies these for DONE chunks — a missing or stale field is a
   gate failure, not a formality.
4. Verify that the chunk has two distinct records:
   - literal source transcription, preserving signs, exponents, modulus,
     labels, and order;
   - normalized ordered step map, with one entry per author inference.
5. Confirm the first author step not yet accepted by Lean. Work only on that
   step; do not write ahead or attack the final theorem directly.

If the exact source is ambiguous, stop before Lean work and obtain a second
visual transcription. OCR or extracted text is navigation help only; the
rendered PDF is authoritative.

## One-step verification loop

For each author step, in source order:

1. Record its source page/region, exact premises, exact conclusion, cited
   result, substitution, and modulus.
2. Run a cheap Sympy witness search when the claim is computational. A
   witness disproves the transcription or step; no witness is only a smoke
   result, never a proof.
3. Encode exactly that step as one named Lean claim. Add only formal details
   that paper convention leaves implicit: casts, nonzero facts, bounds,
   parity, typeclass instances, exponent identities, and cancellation
   conditions.
4. Compile immediately. After an error, do not add later tactics or later
   author steps.
5. Search Mathlib only for the current error or bridge. Search pinned local
   sources first, batch candidate checks into one script, and use one
   container round-trip. Set a bounded search: after local search plus one
   batched candidate check fails, classify the outcome below instead of
   starting open-ended proof research.
6. Save the compiler message, source quotation, and attempted faithful Lean
   encoding as evidence for the classification.

## Mandatory outcome classification: four failures or one success

Every attempted author step must end in exactly one of these five outcomes.
Agents must state the classification explicitly in the chunk notes or
handoff before continuing or stopping.

### F1 — Transcription or chunk-model error

Evidence: the Lean claim, Sympy witness, or second visual check does not match
the rendered PDF; a sign, exponent, modulus, hypothesis, dependency, or step
boundary was copied incorrectly.

Action: correct our transcription/chunk record, rerun the cheap checks, and
retry the same author step. This is the only class in which changing the
formalized statement is routine. Never attribute this failure to the author.

### F2 — Lean encoding or Mathlib API error

Evidence: the paper step is clear, but Lean reports a syntax/type/cast/
instance/normal-form problem, or the attempted Mathlib lemma has the wrong
API. The mathematical implication itself has not been rejected.

Action: repair only the representation or API bridge. Consult the pinned
Mathlib source and project API lessons. Preserve the source claim and its
place in the chain. If the bounded search is exhausted, record the exact
technical blocker and hand it off; do not replace the proof step.

### F3 — Missing explicit side condition

Evidence: Lean exposes a condition the paper treats implicitly, such as a
nonzero divisor, positivity bound, odd exponent, coprimality fact, modulus
reduction, or preservation of hypotheses under a stated substitution.

Action: first trace the condition to existing author hypotheses or a cited
standard theorem. If it follows routinely, encode that derivation immediately
before the step and continue. If it requires a new mathematical assumption or
nontrivial argument absent from the source, reclassify as F4; do not invent it.

### F4 — Faithful author step unsupported

Evidence: transcription has been independently checked; the Lean types and
API bridge are correct; all side conditions justified by the source have been
supplied; yet the stated conclusion does not follow, a counterexample exists,
or a required assumption/inference is absent from the author's text.

Action: stop the chunk at this first unsupported step. Do not prove around it,
strengthen hypotheses, repair a sign, or continue downstream. Mark the chunk
`BLOCKED` and create an author-actionable query according to
`pipeline/05-feedback/README.md`, including the source quotation, plain-language
issue, minimal reproduction/counterexample when available, and Lean error or
unsolved goal.

### S1 — Faithful step verified

Evidence: Lean compiles the claim without `sorry`, custom axioms, changed
hypotheses, or an alternative proof route, and the claim is visibly mapped to
the corresponding author step.

Action: record the accepted step and move to the next author step. A chunk is
DONE only after every step receives S1, dependencies are DONE, Sympy smoke
checks pass, the complete file compiles, and `#print axioms` shows only the
permitted standard axioms.

## Who judges a disputed classification?

Lean is the formal judge of whether the encoded implication typechecks. The
rendered PDF is the authority for what the author wrote. Neither Lean nor an
AI decides authorial intent where the PDF is ambiguous.

A second agent or external model (including Jev, if configured) may act as an
**independent reviewer**, not as an authority. Consult it only after the first
agent has produced a compact evidence packet: source image coordinates and
literal transcription, normalized premises/conclusion, minimal Lean snippet,
compiler output, Sympy result, and proposed F1/F2/F3/F4 classification. The
reviewer must classify independently and may identify a transcription or API
mistake. It may not invent a proof, reinterpret an unexplained sign, or
supersede a Lean failure. If reviewers disagree after checking F1–F3, choose
F4 and ask the author rather than spending more proof-search resources.

## Sequencing and smoke gating

Work one chunk at a time, in strict source order, gating each expensive step
behind a cheap check:

1. Freeze the literal transcription and ordered author-step map.
2. Record and verify all cited dependencies.
3. Sympy-screen the statement and computational intermediate claims.
4. Encode and classify one author step at a time using F1–F4 or S1.
5. Stop immediately on F4; continue only after S1.
6. At chunk completion, compile in the Linux work volume, check for `sorry`
   and unexpected axioms, fill the chunk's evidence fields, then update
   `status.tsv`, chunk YAML, and generated `pipeline/PROGRESS.md`. Finally
   `progress.py --check` must exit 0: it machine-verifies the evidence block
   (extraction binding, page verdicts, render provenance, `lean_decls` in the
   Lean file, no `sorry`).

Run `docker compose exec -T lean sh /workspace/proof/check_env.sh` before any
large work — if it is red, fix the machine, not the math. The default is a
fast compile-free check; `--full` additionally validates `import Mathlib`.

## Cost classes (do the cheap thing on the right side)

- **Transcription:** minutes; done from the PDF renders.
- **Sympy witness search:** cheap; run with the pinned Python toolkit in the
  persistent `lean` container.
- **Mathlib lemma verification:** one slow-ish `lake env lean` round-trip;
  batch all name-checks into ONE script, exec once.
- **Lean compile against Mathlib:** only inside the `lean` container, and
  NEVER on a Windows bind mount (9p drvfs deadlocks the cache fetch).
  Lake work happens in `/workspace/work` (Linux `lake-work` volume);
  `proof/`, `pipeline/`, and `proof_verify/` are source/edit locations only.

## Tooling pitfalls that have already wasted time

- PowerShell does not parse bash-isms: `cat <<EOF`, `&&`, and `| tail`
  fail or misbehave. Use the Linux tool for POSIX commands, or write a
  script file and exec it once.
- Batch container round-trips. One script per session, exec once — never
  one command per round-trip through a fragile shell bridge.
- CRLF: `.gitattributes` forces `eol=lf`. Never add Linux scripts via
  Windows tools that inject CRLF (the `\r` shebang broke `#!/bin/sh`).
- Host shells are not the Linux container: on Windows, PowerShell lacks
  bash-isms, and some agent/harness shell bridges treat `docker compose`
  foreground calls as services and hijack them (ready-polling instead of
  running, observed with the `lean` service in session 4). If a routine
  docker/compose command misbehaves at the shell layer, drive the command
  from the harness's evaluation/sandbox mechanism (one shot) or a script
  file — never restructure the Docker invocation to dodge the bridge.
- Text fidelity: hand-typed accent/diacritic text (e.g. Vietnamese source
  quotes) can corrupt in transit through some tool paths. Keep the literal
  source transcription ONLY in the chunk YAML `source_text` (its schema
  home) and write Lean docstrings / notes in English; never hand-retype
  math or accented prose into docstrings. If a docstring changes, the
  compiled declarations do not change — a re-compile is only needed when
  the proof text changes.
- **PowerShell expands `$?` (and `$(…)`) inside a `docker … sh -c "…"`
  string before it reaches the container.** `echo EXIT=$?` therefore prints
  `True`, which silently destroys exit-code evidence — the failure looks
  like success. Never rely on an exit-code echo inside an inline
  `sh -c` string: write the script to a file (pipe it in and strip CR with
  `tr -d '\r'`) and/or redirect the command's output to a container-side
  file and read that back.
- **`docker compose exec -d` is NOT a safe way to run a long build.** The
  in-container process dies when the client detaches; three `lake build`
  runs were killed this way. Use a tracked background task (the harness
  keeps the client alive) with output redirected to a container-side file,
  then poll the file. Also: a tracked background task's own log file can be
  EMPTY for `docker compose exec` (buffered output is not captured) — the
  container-side file is the reliable evidence channel.
- **A killed build leaves poisonous state, not just missing output.** A
  `lean_lib` build dir containing `.ilean` / `.trace` / `.olean.hash` but no
  `.olean` makes Lean fail with "object file … does not exist" *instead of*
  falling back to compiling the source — so a consumer's `import` breaks
  until the producer is rebuilt. Remedy: recompile the producer (harness, or
  `lake build Lk`). Do NOT read this as a Mathlib/toolchain problem, and do
  not reach for `docker compose down -v` / image rebuild / `cache get` —
  see the import-failure triage in `ENCODING_MAP.md` §A.
- **Foreground tool timeouts kill `lake` mid-round.** Two `lake build` +
  probe chains exceeded the 10-minute cap and were killed; one a few seconds
  short of finishing. Split long chains, or run them as tracked background
  tasks with container-side output capture.
- **One probe round beats one round per wrong name.** A single batched
  `#check @` file pinned 42 of 43 intended names before the first author
  step (L4-01 rounds 1 and 3). The `import Mathlib` elaboration is the whole
  per-round cost, so the real lever is the NUMBER of rounds: probe in bulk,
  then one step per compile.
- **A probe file's `#check` list is trustworthy only if it actually ran.**
  `proof/NameCheck.lean` was never executed, and its list is the source of a
  falsified recipe (`ZMod.intCast_zmod_eq_zero_iff_dvd`) that cost a
  round-trip; `03-lean/L4Probe.lean` and `L6Probe.lean` were each executed
  once and then deleted, so the names they pinned are not archived anywhere.
  Re-check names against the pinned Mathlib source and re-run a bulk `#check`
  in the container instead of trusting a stale list.
- **Two sessions in one repo share write targets** (`status.tsv`,
  `PROGRESS.md`, `HANDOFF.md`, `lakefile.toml`). An edit is rejected as
  stale when the other session has written the file since your last read —
  re-read and re-apply ONLY your own paragraph, never wholesale. Do not
  commit while another session has uncommitted edits in those files (a
  status sweep once captured another lane's ledger row). A
  concurrent compile session also roughly triples per-round wall time
  (922 s measured while two sessions compiled).
- **Cheap habit that keeps paying:** after `rw [h, mul_zero] at hyp`, `hyp`
  is already `x = 0`, so `hx hyp` is right and `hx hyp.symm` is a type
  error. This reversal cost a round in two different steps (L4 S3 and S4).

## Where the contracts live

- `pipeline/PIPELINE.md` — stage-by-stage pipeline description.
- `pipeline/02-chunks/schema.md` — chunk record contract (DONE criteria).
- `pipeline/02-chunks/chunks/*.yml` — per-chunk records.
- `pipeline/05-feedback/README.md` — author-feedback triage and format.
- `pipeline/progress.py` + `pipeline/PROGRESS.md` — live status dashboard.
- `README.md` — quick start and environment.
- `pipeline/03-lean/MATHLIB_API_LESSONS.md` — Mathlib API pitfalls and
  workarounds discovered during the first chunk (ZMod, linarith, pow_mul,
  FLT). **Read this before encoding any Lean proof.**
- `pipeline/03-lean/ENCODING_MAP.md` — the PDF's notation → Lean/Mathlib
  term mapping (gcd, `⋮`, congruences, "chứng minh tương tự", …) plus the
  proof patterns that already compiled, one section per chunk. Read
  alongside the API lessons; append a section per new chunk.
- `.github/skills/fermat-lean-mathlib/SKILL.md` — the project's Lean 4 +
  Mathlib skill: toolchain pin, container compile loop, lemma-search
  ladder, naming conventions, error→fix table. **Loading this skill
  (`SKILL.md` + `references/search.md` + `references/reference.md`) is
  MANDATORY before any Lean work** — see "Required preparation" above.
  It is a gate, not optional background reading.

Daily work uses the persistent `lean` service and named volumes; image builds
are exceptional maintenance. See `README.md` for runtime commands and
`docs/IMAGE_BUILD.md` for Dockerfile layering and rebuild guidance.