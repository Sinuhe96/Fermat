# Lemma search playbook (verified against this repo's pin)

Order: cheapest and most pin-accurate first. Every command here was run
in this environment (`lean` container, Mathlib `v4.35.0-rc2`, rev
`06535612…`).

## 1. Grep the local Mathlib source (pin-exact, offline, instant)

The full Mathlib `.lean` source tree ships with the build — this is the
ground truth for OUR pin:

```sh
docker compose exec lean grep -rn "theorem pow_card_sub_one_eq_one" \
  /workspace/work/testproj/.lake/packages/mathlib/Mathlib/
```

Verified hit: `Mathlib/FieldTheory/Finite/Basic.lean:218` (general field
version) and `:611` (`ZMod p` specialization).

When to use: you half-remember a name, want every lemma mentioning a
symbol (`Int.ModEq`, `ZMod`), or the docs website disagrees with us
(docs track newer Mathlib). Grep beats every web tool on precision
because it reads exactly what we compile against.

From the Windows host (no container round-trip), the same tree is at:
`proof_verify/.lake/packages/mathlib/Mathlib/` (read-only browsing OK;
never run `lake` there — 9p deadlock, see AGENTS.md).

## 2. Loogle JSON API (structured search, works from inside container)

Verified working:

```sh
curl -s "https://loogle.lean-lang.org/json?q=Int.ModEq"
```

Returns JSON: `{"count": N, "hits": [{"name", "type", "module", "doc"}…]}`.
Query forms: type patterns (`(?a -> ?b) -> List ?a -> List ?b`),
comma-separated symbol list (`Int.ModEq, Nat.Prime`), or quoted substring
(`"modEq"`). Add one filter at a time — over-filtering returns 0 hits.
Web UI: <https://loogle.lean-lang.org/>.

## 3. In-editor search tactics (inside a .lean file)

These search the environment we actually compiled — best signal for
"what closes THIS goal":

- `exact?` — lemma that finishes the goal from context.
- `apply?` — lemmas applicable to the goal (superset of `exact?`).
- `rw?` — rewrites for the goal (also `rw? at h`).
- `simp?` — emits the exact `simp only [...]` used.

Batch them in one file, run one `lake env lean` (see SKILL.md §Compile).
`Try this:` suggestions are clickable in an IDE; in batch mode, read them
from stdout and paste.

Probe evidence at this pin (2026-09-25, one file, four searches):
`exact?`, `rw?`, `apply?` each CLOSED their goal and printed a
suggestion; `simp?` printed `simp only [add_zero]` but left the goal
open (`⊢ n = 0`) because the local hypothesis `h` was not in the emitted
list — pass local hypotheses explicitly (`simp? [h]`) or follow with
`exact h`. Also: each search tactic scans the whole environment — that
4-search file took 413 s wall while another compile contended for the
container's 6 GB. Expect seconds-to-minutes per search, not interactive
latency; do not run two `lake env lean` jobs concurrently.

Caveat: `exact?` needs the goal's *exact* shape in the library — if it
finds nothing, normalize first (`norm_cast`, `mul_comm` alignment) or
state the subgoal as its own `have` and search again.

## 4. Natural-language search

- Web: <https://leansearch.net/> (NL queries), <https://www.moogle.ai/> —
  or `read` these URLs directly. Loogle web UI: <https://loogle.lean-lang.org/>
  (JSON API in §2 works from the container).
- **Do NOT use the in-file `#loogle "…"` / `#leansearch "…"` commands in
  this container** — they hang. Observed twice at this pin: a file with
  just `import Mathlib` + these two commands failed to finish in 600 s
  (and 300 s on an earlier attempt), while the offline-only file
  completed under the same conditions and `curl` to the same Loogle host
  returned in seconds. Lean's HTTP client appears to stall here. Stick
  to `curl` (§2) and the web UIs.

NL results are ranked by embedding, not checked — always confirm a
candidate with `#check @name` in a batch (§Batch rule).

## 5. Docs and community

- Docs (our-nearest build): <https://leanprover-community.github.io/mathlib4_docs/>
  — search bar = substring match on names. May be newer than our pin;
  confirm against local source when it matters.
- Naming rules (to *guess* names): see `reference.md` §Naming, official
  page <https://leanprover-community.github.io/contribute/naming.html>.
- Zulip `#Is there code for X?` — human fallback, hours not seconds.

## Batch rule (from AGENTS.md cost classes)

All name checks go in ONE .lean file, ONE `lake env lean` round-trip:

```lean
import Mathlib
#check @Int.ModEq.dvd                      -- from MATHLIB_API_LESSONS.md
#check @ZMod.intCast_zmod_eq_zero_iff_dvd  -- probe-verified at this pin
#check @ZMod.pow_card_sub_one_eq_one       -- confirmed by local-source grep
```

Never one round-trip per lemma. Template lives at `proof/NameCheck.lean`.
