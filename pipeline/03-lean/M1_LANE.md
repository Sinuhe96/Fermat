# M1_LANE.md — main-proof lane state (PDF pp. 6–33)

Live state for the lane that verifies the author's main proof (printed
section `D. CHỨNG MINH ĐỊNH LÝ LỚN FERMAT`, pp. 6–33). Binding rules:
`AGENTS.md` — one-step loop, F1–F4/S1 classification, leaf cap ≤ 2 PDF pages
/ ≤ 10 author steps / ≤ 300 Lean lines, `kind: section-assembly` per author
section. This file is the orchestrator's durable memory; `progress.py --check`
remains the machine gate per chunk.

Lane open 2026-09-28. Bootstrap gates at open: `proof/check_env.sh` SMOKE
PASS; `pipeline/progress.py --check` exit 0 with 13/13 DONE (L1–L7,
L7-FRAG-01…06, L7-ASM), 0 OPEN obstacles, 0 OPEN author queries.

## 0. Time box and evidence constants

Time box (user-set): lane open 2026-09-28T02:58:47Z (epoch 1790564327), hard
stop 2026-09-28T04:58:47Z (epoch 1790571527). At the stop: keep every file,
write the progress/problems report into §7 below and into `HANDOFF.md`.

Evidence constants — every M1 chunk's evidence block is bound to these:

| field | value |
|---|---|
| `source_pdf_sha` | `721c25390d164787b1f645cdc7eeb19e7a39444879811ebe761b982823a88761` (identical in all 33 region records) |
| `extract_run_sha` | `f25efc62f3487b998b82a1936c858650030304dc57ec5d845a7193f8beabe4e1` (sha256 of `01-extract/out/extract_meta.json`) |
| `fidelity` | `PASS_WITH_MANUAL` (19 manual pages, 0 failing) — re-verified at lane open |
| `transcription` | `manual` (mandatory where the page verdict is MANUAL) |
| crops | `pipeline/01-extract/out/page-NNN-300dpi-region-NN.png`; any leaf touching a MANUAL page records its render reads in `renders` |

## 1. Round protocol — one compile per round, strictly serialized

Cost model at this pin: one warm `import Mathlib` round is 250–400 s, and a
second concurrent `lake env lean` roughly triples it (922 s measured). The
lane therefore never runs two compiles at once and must not share the
container with another compiling lane.

**Before a round (hard gate, no exceptions):**
1. `tail -n 5 pipeline/03-lean/M1_watch.log` — any `LATCH <seq>` newer than
   the last `ACK <seq>` stops the lane until explained (ENV-DOWN /
   CONTENTION / STALL / OVERRUN / DISK). Fix the machine, not the math.
2. Read the breaker table (§3). A tripped threshold stops the lane.
3. **Before writing any call site:** read the producer's header in
   `SIGNATURES.md` and check its four traps — coordinate, modulus (`n` vs `n²`
   vs `n^{4s+2}`), form (`≡` vs `- ≡ 0` vs `∣`), orientation. The sheet is
   generated (`python pipeline/03-lean/gen_signatures.py`, after every DONE
   flip), so it cannot drift from the sources, and its `probes/SIGNATURES.probe.log`
   carries the *elaborated* types. Its own header records that call-site shape
   caused **every** error round of the L7 lane; a header read costs seconds
   against a 250–400 s round.
4. Write `pipeline/03-lean/M1_inflight` = `<round>\t<epoch>\t<file>`.

**Two probe layers, and they do not overlap (measured: 0 shared names).**
`probes/SIGNATURES.probe.lean` (generated) pins the **project** declarations
this lane must call — 118 of them, in `SIGNATURES.md` with their source
signatures. `probes/M1-LANE.probe.lean` (hand-written, round-1 S1) pins the 51
**Mathlib/toolchain** names the main proof needs (`add_pow`, `Nat.choose_*`,
`Int.ModEq.*`, `pow_add`, the `Finset.sum_*` family). Keep both; neither
substitutes for the other.

**After a round:** append one row to `M1_rounds.tsv`, delete `M1_inflight`,
record the F1–F4/S1 class of the step, then — and only then — write the next
author step.

## 2. Wall-clock reporting

The watchdog emits a `REPORT` line every 1800 s; rounds are 5–7 min, so a
round boundary lands inside every 30-minute window. At that boundary the
orchestrator emits a status block: elapsed, rounds used, S1 steps accepted,
consecutive failed rounds, current chunk/step, latch state. Numbers come from
`M1_watch.log` + `M1_rounds.tsv`, never from recollection.

## 3. Circuit breakers — stop the lane, never retry around them

| condition | threshold | action |
|---|---|---|
| latch newer than last ACK | any | stop; diagnose env; `ACK <seq>` in `M1_watch.log` |
| consecutive failed rounds on ONE author step | ≥ 3 | observer consult (§4), then AGENTS.md bounded search: local `rg` + ONE batched candidate check, then classify F1–F4 |
| rounds spent on one leaf | > 30 (L5 needed 29) | re-split the leaf under the leaf cap |
| error sites in one round | > 8 | decompose the step (L7-FRAG-01 round 1: batching cascades) |
| wall clock on one leaf | > 240 min | observer consult |
| `progress.py --check` red after a DONE flip | any | fix the evidence block before opening the next chunk |

## 4. Observer — independent reviewer, invoked on a breaker only

Per AGENTS.md "Who judges a disputed classification": the orchestrator hands
the observer a compact packet — source region id + signed-LaTeX quotation,
normalized premise/conclusion, exact Lean snippet, compiler output, sympy
result, proposed class. The observer returns exactly one verdict:

`CONTINUE` | `REPAIR-PLAN <n>` | `RECLASSIFY <F1|F2|F3|F4>` | `ESCALATE-ENV` | `RESPLIT`

The verdict binds the next round. `RECLASSIFY F4` stops the chunk and files
an author query per `pipeline/05-feedback/README.md`. The observer never
invents a proof, never reinterprets an ambiguous sign, and never supersedes a
Lean failure.

Honest limit: a subagent cannot preempt a command already in flight, so stop
enforcement happens at round boundaries — the only place a stop is
actionable. The mechanical watchdog (`proof/watch_lane.sh` → `M1_watch.log`)
covers the between-rounds environment and duration conditions, so a hung
container is latched even while the orchestrator is blocked in a round.

## 5. Chunk plan

Consolidated 2026-09-28 from the six scout reports (`M1_scout/*.md`); ids here
are **final** in source order, the scouts' provisional ids are in their files.
`kind` is `lemma-proof-step` unless stated; assemblies are `section-assembly`.

Packing rule that sets the sizes: one compile round costs 250–400 s
*regardless of the leaf's size*, so a leaf is packed toward ~8–10 author steps —
the AGENTS.md cap (≤2 pages / ≤10 steps / ≤300 lines) is a ceiling, not a
target. Scout step counts are the conservative reading; a leaf may merge with
its neighbour at DONE time if the combined step count stays ≤ 10.

**Scale estimate (honest):** 41 leaves + 1 prerequisite + ~6 assemblies. At the
measured 5–9 rounds per leaf, that is roughly **250–400 container rounds ≈
20–35 h of wall time**, plus the crop reads. This is a multi-session lane; the
2-hour window covers the plan, the prerequisite chunk, and the numeric screens
only.

### Prerequisite (p. 2)

| id | pages | regions | steps | depends_on | content |
|---|---|---|---|---|---|
| `B-01` | 2 | P002-R1 | 3 | — | section B: `B.1` index shift, `B.2` falling-factorial sum `= f^(k)(x)`. **Required by every M1 leaf from p. 9 on** — citations at P009-R3, P010-R1, P011-R6/R7/R9, P013-R1, P014-R1/R2. Crop read done + sympy green; `03-lean/B/Basic.lean` not yet written. |

### Leaves in source order

| id | pages | regions | steps | depends_on | content |
|---|---|---|---|---|---|
| `M1-FRAG-01` | 6 | P006-R1 | 5 | L1-01, L6-01 | bổ đề 6 substituted, WLOG `u,v ≢ 0`, `(3)` rewritten |
| `M1-FRAG-02` | 6 | P006-R2 (l1 + the (7′) tail of l4–6) | 2 | 01 | printed (7), (7′) — **needs the equation as hypothesis** (§7). Boundary revised down from 5 steps: (8),(9),(10) are the same computation at higher orders and belong to 03. |
| `M1-FRAG-03` | 6 | P006-R2 (l7–9) | 3 | 01 | printed (8), (9), (10) — **DONE**, round 28 (R3 l1 moved to `M1-FRAG-04`) |
| `M1-FRAG-04` | 6–7 | P006-R3 (l1–5), P007-R1 (l0–l6) | 5 | 03 | the `l+j` regrouping; **DONE** (rounds 34–55, 16 declarations, 5 steps all S1: the expansion, the binomial RHS, the `l+j ≥ 5` split with the `(j,l,i)` re-indexing, the absorbed tail + four explicit terms, the five X⁴ sums in factorial form). Regions MEASURED: `P007-R1` l0–l6 is what this leaf needs (l4–l6 = S3, l6+ = S4's display) |
| `M1-FRAG-05` | 7 | P007-R2 (l0–l3) | 4–10 | 04 | **the ten remaining binomial→factorial conversions** (X³: 4 sums, X²: 3, X¹: 2, X⁰: 1), the continuation of `M1-FRAG-04`'s S4 display. Regions MEASURED 2026-09-28 — the earlier `R1 l5–7, R2 l1–5` came from estimated line numbers and cut across two displays |
| `M1-FRAG-06` | 7 | P007-R2 (l4–l5), P007-R3 (l0–l4) | 3 | 05 | the RHS tail restatement + the `⇒` display rearranging the X⁴ sums (`i(i+1)(2+i)(3+i)`, `-n/6 Σ[3i(i+1)(i+2)+3i(i+1)+2i]`, …). R3 l0–l4 continues R2 l6 — ONE display across the page break |
| `M1-FRAG-07` | 8 | P008-R1 (l0–l1), P008-R2 (l0–l2) | 3 | 06 | the first **congruence** `≡ … (mod n^{4s+2})` (with the printed `vì 5s ≥ 4s+2, s ≥ …`) followed by the `⇒` rearrangement of the X⁴ sums. Congruence steps are where a dropped term needs a divisibility side condition — the F3/F4 risk of this part |
| `M1-FRAG-08` | 8 | P008-R2 (l3)–P008-R3 (l5) | 4 | 07 | second `≡ (mod n^{4s+2})`, the `⇒` rewrite splitting `Σ[3i(i+1)(i+2)+3i(i+1)+2i]` into three sums, third `≡ (mod n^{4s+2})` |
| `M1-FRAG-09` | 9 | P009-R1 (l1–7) | 7 | 08 | `M`, display (11) |
| `M1-FRAG-10` | 9 | P009-R2 (l1–8) | 8 | 09 | `B`, `C`, `D`, `E`, `F` definitions; the **"Quy ước"** on denominators |
| `M1-FRAG-11` | 9–10 | P009-R3 (l1–5), P010-R1 (l1–3) | 8 | 10, **B-01** | first `mục B.1/B.2` application |
| `M1-FRAG-12` | 10 | P010-R1 (l4–12) | 9 | 11 | |
| `M1-FRAG-13` | 10 | P010-R1 (l13), P010-R2 (l1–7) | 8 | 12 | `M_1` |
| `M1-FRAG-14` | 11 | P011-R1–R3 | 7 | 13 | |
| `M1-FRAG-15` | 11 | P011-R4–R6 | 6 | 09, **B-01** | |
| `M1-FRAG-16` | 11 | P011-R7–R9 | 8 | 15, **B-01** | ends the pp. 6–11 prelude |
| `M1-FRAG-17` | 12–13 | P012-R1–R3, P013-R1 head | 8 | 16 | `B^*` → `B = B₁+B₂+B₃`; **crop** (P012 sign/n jump) |
| `M1-FRAG-18` | 13–14 | P013-R1 tail–R4, P014-R1 head | 9 | 17 | `C`, `C₁`, `C₂`, `C₃`; cites §B.2 |
| `M1-FRAG-19` | 14 | P014-R1 | 8 | 18 | `D` closed form; cites §B.1 + §B.2 |
| `M1-FRAG-20` | 14 | P014-R2, R3 | 6 | 19 | `E` closed form, `F` opening |
| `M1-FRAG-21` | 15 | P015-R1–R3 | 9 | 20 | `F` middle; **colour carries the moves → crops** |
| `M1-FRAG-22` | 16–17 | P016-R1–R3, P017-R1 | 9 | 21 | `F ≡ F₁+F₂+F₃ (mod n^{4s+2})`; **crops** (P016 exp turnover, PUA digit) |
| `M1-FRAG-23` | 17 | P017-R2, R3 | 8 | 17–20, 22 | `P`, `Q`, `T`, congruence **(12)** |
| `M1-FRAG-24` | 18 | P018-R1–R3 | 3 | 23 | `N := n^s·abck`, `P₁`, `P₂` |
| `M1-FRAG-25` | 19 | P019-R1–R3 | 4 | 24 | `P₁` completion, `P₂` |
| `M1-FRAG-26` | 20 | P020-R1–R3 | 6 | 25 | `G`, (14), (15) |
| `M1-FRAG-27` | 21 | P021-R1–R3 | 4 | 26 | common denominator `6(h−b^n)³`; `=` vs `≡` per line → **crop** |
| `M1-FRAG-28` | 22 | P022-R1–R3 | 7 | 27, 23, 16 | `T`, `Q₁`, `M(N)⁴`; **crop** (dropped factor `n`) |
| `M1-FRAG-29` | 23 | P023-R1–R4 | 5 | 28, 23 | six re-expansions, `Q`; **crop — candidate F4** |
| `M1-FRAG-30` | 24 | P024-R1–R3 | 2 | 29 | `R` (definition seam with p. 23) |
| `M1-FRAG-31` | 25 | P025-R1, R2 (d0–d2) | 1 | 30 | |
| `M1-FRAG-32` | 25–26 | P025-R2 (d3–d7), R3, P026-R1 (d0–d2) | 2 | 31 | **crop — candidate F4** (`2n(n−1)` vs `2(n−1)`) |
| `M1-FRAG-33` | 26–27 | P026-R1 (d3–d7), R2, R3, P027-R1 | 2 | 32 | |
| `M1-FRAG-34` | 27 | P027-R2, R3 (d0–d2) | 1 | 33 | **crop** — label **(10)** vs content of (7) |
| `M1-FRAG-35` | 27–28 | P027-R3 (d3–d6), P028-R1–R3 | 3 | 34 | closes the prelude, opens §1.1 |
| `M1-FRAG-36` | 29–30 | P029-R1–R3, P030-R1, P030-R2 head | 8 | 35 | §1.1: (16′), (16″), `H(h,b)`, (17), (17′) |
| `M1-FRAG-37` | 30–31 | P030-R2 tail, R3, P031-R1 | 5 | 36, **L7-ASM** | bổ đề 7 use **#1** → (18)–(22′), `n ≡ 1 (mod 6)` |
| `M1-FRAG-38` | 31 | P031-R2, R3 | 9 | 37 | (23), (24), (25); `(26)` cited but never printed → §7 |
| `M1-FRAG-39` | 32 | P032-R1 head … "n = 3, vô lý" | 6 | 38, **L7-ASM** | bổ đề 7 use **#2**; the **(27) cancellation must be proved** → §7 |
| `M1-FRAG-40` | 32–33 | P032-R1 tail, R2, R3, P033-R1 | 9 | 36, L6-01 | (28)–(32), (17″), (17‴) |
| `M1-FRAG-41` | 33 | P033-R2 | 6 | 39, 40, L1-01, L2-01 | **final assembly home** ("Vậy định lý lớn Fermat đã được chứng minh") |

### Assemblies

| id | covers | kind | note |
|---|---|---|---|
| `M1-ASM-A` | pp. 6–28 (leaves 01–35) | section-assembly | the prelude to §1.1: one long computation, no printed heading |
| `M1-ASM-B` | pp. 29–30 (§1.1) | section-assembly | `H(h,b)`, `H(h,a)` properties (17), (17′) |
| `M1-ASM-C` | pp. 30–32 (§1.2, `h = c^n`) | section-assembly | bổ đề 7 use #1 + the (27) cancellation |
| `M1-ASM-D` | pp. 32–33 (§1.3, `h = n^{ns−1}c^n`) | section-assembly | (28)–(32) |
| `M1-ASM-E` | p. 33 (§2, `n` prime < 13) | section-assembly | carries the Dirichlet/Lamé/Kummer citations **as hypotheses**, never axioms |
| `M1-THM` | pp. 6–33 | section-assembly | the theorem: case split `n > 11` vs `n < 13`, home region P033-R2 |

Assembly boundaries are provisional until the bordering leaves reach DONE (the
printed section/case markers were read at scout level only).

## 6. Artifacts of this lane

- `M1_rounds.tsv` — one row per compile round (machine-readable ledger).
- `M1_watch.log` — mechanical heartbeat / latch log (`proof/watch_lane.sh`).
- `M1_inflight` — in-flight round handshake (transient).
- `M1_scout/*.md` — read-only inventories of pp. 6–33 (scout wave).
- `probes/M1*.probe.lean|.log` — archived probe pairs (never imported, never
  in `lakefile.toml` / `Main.lean`).
- `04-sympy/test_m1_*.py` — per-leaf numeric screens.
- `02-chunks/chunks/M1*.yml` + `02-chunks/status.tsv` — the chunk records.

## 7. Findings and problems (running log)

**F1 (ours — caught before any Lean work, fixed) — the p. 6 screen first
omitted the equation hypothesis.** The first draft of
`04-sympy/m1_common.py` asserted
`h^n − a^(n^2) − b^(n^2) ≡ n[…]X (mod n^(2s+1))` as an *unconditional*
congruence; it failed all 150 instances. It is not unconditional: that
statement is `Σ_{i≥1} term(i) ≡ term(1)`, which uses the equality
`h^n − a^(n^2) − b^(n^2) = Σ_{i≥1} term(i)` — available only *under* (3)
`u^n + v^n = t^n`. What is unconditional is the **tail** divisibility
`Σ_{i>order} term(i) ≡ 0 (mod n^((order+1)s+1))`, since for prime `n` every
`C(n,i)` with `1 ≤ i ≤ n−1` carries one factor `n` (and each `X^i` carries
`n^(i·s)`).

Consequences the Lean lane must honour: (a) the leaf encoding (7)–(10) takes
`(b^n+X)^n + (a^n+X)^n = (h−X)^n` as a **hypothesis** — those displays are
conditional on (3), not identities; (b) only the tail statement is
screenable, and that is what `m1_common.screen_tail` checks; (c) the outer
hypotheses are vacuous (`fermat_box_count` = 0 for n ≥ 3), so nothing
downstream of (3) is.

**Boundary note (not an author error, no query).** At `order = n−1` the last
summand `i = n` has `C(n,n) = 1` and reaches only `n^(n·s)`, so the printed
modulus `n^((order+1)s+1)` is not implied there — falsified at `n = 5`,
order 4. The author's `n > 11` keeps `order ≤ 4 ≤ n−2`, so the printed
displays are unaffected. `screen_tail` records the boundary explicitly
instead of quietly skipping `n = 5`.

**Verified numerically so far (unconditional):** the expansion identity is
exact, and `tail(order) ≡ 0 (mod n^((order+1)s+1))` for orders 0–4 on 6
instances each at `n ∈ {5,7,11,13,17,19,23}`, printed moduli sharp —
`docker compose exec -T lean python /workspace/pipeline/04-sympy/m1_common.py`
→ PASS, EXIT 0. Also PASS: the p. 6 triple-sum regrouping (all 10 printed
index ranges are the natural `[l, n−1−j]`, the partition is exact, the
residual is non-vacuous), p. 7 R1's RHS, and section B's two rules.

**STRUCTURAL — section B is an unverified dependency of the main proof.**
The document is `A. CÁC BỔ ĐỀ` (lemmas), `B. MỘT CÁCH BIỂN ĐỔI TỔNG Σ₃ VÀ MỘT
DẠNG TÍNH ĐƯỢC CỦA TỔNG Σ₃` (two sum-transformation rules), `C. CHỨNG MINH CÁC
BỔ ĐỀ` (proofs of lemmas 1–7 — what chunks `L1-01`…`L7-ASM` verify), `D.` (the
main proof). **Section B sits in `P002-R1` and is not chunked.** The main proof
cites it repeatedly — `mục B.1` / `mục B.2`, always with `trang 2`: hits in
`p009.yml` (2), `p010.yml` (1), `p011.yml` (4), `p013.yml` (1), `p014.yml` (3).
The two rules are

* `B.1` `Σ_{i=k}^{n} a_i = Σ_{i=m}^{n+m−k} a_{i−m+k}` (pure re-indexing);
* `B.2` `Σ_{i=k}^{m−1} i(i−1)…(i−k+1) h^{m−1−i} x^{i−k}
  = Σ_{i=0}^{m−1−k} (m−1−i)…(m−k−i) h^i x^{m−1−k−i} = f^{(k)}(x)` with
  `f(x) = Σ_t x^{m−1−t}h^t = (x^m − h^m)/(x − h)`.

Both screen true (`m1_common.screen_section_B`: `B.1` on 50 random instances,
`B.2`'s middle form as the same sum read backwards and its last form as the
k-th derivative, exact for `m ≤ 7`, `k ≤ 4`). **Plan amendment:** add chunk
`B-01` (`kind: lemma-statement`, `pdf_pages: [2]`, `regions: P002-R1`,
`transcription: manual`, `depends_on: []`) and make it a prerequisite of every
M1 leaf that cites B.1/B.2 — i.e. all leaves from p. 9 on. Leaves covering
pp. 6–8 do not need it. It is small (two identities) and it is on the critical
path of the whole main proof, so it is scheduled before them.

**pp. 12–17 carry a transcription risk that the signed LaTeX does not record.**
Scout report (`M1_scout/pp12-17.md`): the range is one unbroken `§D.1`
computation (no printed heading between p. 6 and p. 29), 33+ displays, in which
red/green/blue/magenta/cyan emphasis marks *which summand moves in the next
`=`*, and that emphasis is not encoded in the region records (region notes only
record headings' colour). Two consequences: (a) the transcription of those
leaves must be checked against the 300 dpi crops before Lean work (the scout
lists the crops); (b) one printed pair is *not equal as written* — `P012-R2`
re-enters a term as `+n²[…]/(b^n−h)²` where `P012-R1` had
`−[…](h−b^n)/(h−b^n)³` — so that leaf must transcribe each region's own printed
form and classify the discrepancy (F1/F2), never bridge it by guesswork. This
is the first place in the lane where the "render read" evidence field is
load-bearing rather than a formality.

**Cross-print misprint, confirmed numerically: `C₃` at `P014-R1` vs `P023-R1`.**
Both regions carry the same auxiliary quantity, multiplied in both places by the
same remaining factor `(2 n^s abck)/(h − b^n)^3`:

* `P014-R1` — `5n[h^{n−2} − b^{n(n−2)}] + 2n b^n h[h^{n−4} − b^{n(n−4)}]`
* `P023-R1` — `[−5n h^{n−2} + 2n b^n h^{n−3}] + [5n b^{n(n−2)} − 2n h b^{n(n−3)}]`

Normalising the printed spellings (`b^n h^{n−3} = h^{n−3} b^n`, and
`b^n h b^{n(n−4)} = h b^{n(n−3)}`) leaves exactly two terms sign-flipped.
`04-sympy/triage_c3.py` (EXIT 0) measures it at `n = 13, 17, 19`: the difference
is `10n(h^{n−2} − b^{n(n−2)})` — non-zero, and **not** a global sign flip, since
the terms `2n b^n h^{n−3}` and `−2n h b^{n(n−3)}` are common to both prints. The
companion groups over `(h − b^n)^2` are **identical** (`P014 − P023 = 0` exactly
at all three `n`), which is what rules out a mere denominator convention
(`(h−b^n)^k = (−1)^k(b^n−h)^k`). So one of the two regions misprints two signs
and the p. 14 / p. 23 leaves cannot both be stated as printed. **Triage: candidate
F4** (a printed-vs-printed inconsistency inside the author's own text — our
transcription is not in question, both LaTeX blocks are signed and both were
crop-confirmed). It is deliberately *not* filed yet: the derivation that would
decide which print is wrong sits in a region not yet transcribed (p. 13, or
pp. 21–22), and `C₃` is consumed inside printed denominators
(`P014-R1`'s `D` chain; `P023-R1`'s `Q = Q₁ + M₁X⁴ + ½B₃X³ + ⅙C₃X³`), so the
discrepancy cannot be absorbed by a modulus. File the query at whichever of
those two leaves is reached first.

**Two follow-ups to the `C₃` finding (same script, `triage_c3.py` EXIT 0).**

1. *Majority evidence: `P014-R1` is the outlier.* The `C₃` bracket text is
   **identical** at `P023-R1`, `P023-R2` and `P024-R1` — all three print
   `[−5n h^{n−2} + 2n b^n h^{n−3}] + [5n b^{n(n−2)} − 2n h b^{n(n−3)}]`, and
   `P023-R2`/`P024-R1` show it entered into the `Q`/`Q+T` assembly as `C₃/6`
   with the `(n^s abck)` power accounted for. Only `P014-R1` differs. So the
   author's own text agrees 3-to-1 against the p. 14 print: the query to file
   should say *p. 14 misprints two signs*, not "p. 14 and p. 23 disagree".
2. *A second instance of the same class, `P023-R2` vs `P024-R1`.* This is the
   scout's flagged "the `7` covers only three of four summands". `P023-R2`
   prints
   `[7b^{n(n−4)}(b^n−h)^3 + 7b^{n(n−3)}(b^n−h)^2 − 7b^{n(n−2)}(h−b^n) + h^{n−1} − b^{n(n−1)}]/(h−b^n)^4 · n(n^s abck)^4`,
   i.e. the leading `7` reaches only the first three summands, while `P024-R1`
   writes the same expression with the last two **inside** the bracket,
   `−(−7b^{n(n−4)}(h−b^n)^3 + 7b^{n(n−3)}(h−b^n)^2 − 7[b^{n(n−2)}(h−b^n) + h^{n−1} − b^{n(n−1)}])/(h−b^n)^4`.
   Normalising both to `(h−b^n)`, the two printed numerators differ by a
   **non-zero** polynomial at `n = 13, 17, 19` (the script prints its factored
   form). A first version of this check asserted the closed form
   `8(h^{n−1} − b^{n(n−1)})` and was **falsified** by it; that mis-derivation was
   ours, not the print's, and the check now tests non-vanishing only. Both
   findings are the same failure mode (a printed factor
   that fails to distribute over a bracket), which is worth telling the author
   once, as one query covering the p. 14, p. 23 and p. 24 leaves.

**Third instance of the same class, and it corrects a lane assumption: the
magenta term at `P025-R1` vs `P026-R2`.** The flagged `2n(n−1)` vs `2(n−1)`
question is settled by the signed LaTeX itself, because both regions carry the
term **with its colour markup**:

* `P025-R1` — `\textcolor{magenta}{\frac{2n(n-1)[b^{n(n-2)}+a^{n(n-2)}-h^{n-2}](n^sabck)^4}{(h-b^n)^3}}`
* `P026-R2` — `\textcolor{magenta}{\frac{2(n-1)[b^{n(n-2)}+a^{n(n-2)}-h^{n-2}](n^sabck)^4}{(h-b^n)^3}}`

Same bracket, same denominator, same colour, and the coefficients differ by
exactly a factor `n`. So this is not a colour-reading problem and not a
region-boundary problem: it is a third same-class disagreement, and the earlier
statement in this section that "the colour is not in the signed LaTeX" is **too
strong** — p. 25 and p. 26 do record inline `\textcolor{magenta}{…}`,
`\textcolor{blue}{…}` and `\mathbf{…}` spans. The correction matters, because
where colour *is* recorded it answers the "which term moves" question outright,
and it should be checked per region rather than assumed absent.

Why the factor `n` matters: the term is `2(n-1)(…)·n^{4s}(abck)^4/(h-b^n)^3`, so
the version with the extra `n` is divisible by `n^{4s+1}` while the other is not;
modulo the printed `n^{4s+2}` neither is zero, so the two readings are genuinely
different statements and the leaf cannot absorb the difference.

**Three findings, one failure mode.** `C₃` (p. 14 vs pp. 23–24), the `7…`
bracket (p. 23 vs p. 24) and this coefficient (p. 25 vs p. 26) are all a printed
factor that reaches some summands and not others, in a computation the author
re-prints as he carries it forward. That is a single, well-formed question for
the author, and it should be asked once with all three instances and their
measured differences attached.

**`P027-R3` — resolved, and it is a label reuse, not a gap.** The region prints,
in red, labelled **(10)**:

`h^n − a^{n²} − b^{n²} ≡ n[a^{n(n−1)}+b^{n(n−1)}+h^{n−1}] n^s abck (mod n^{2s+1})`

That is **verbatim p. 6's (7)** (region `P006-R2`), same bracket, same modulus
`n^{2s+1}` — while p. 6's own label (10) belonged to the `n^{5s+1}` display. So
the author re-uses the number (10) on p. 27 for the (7) congruence. Classification:
**not F4.** No false claim and no unsupported inference is involved; the content
is unambiguous and already verified, so this is a **citation hazard only** — a
leaf citing "(10) at p. 27" must cite the (7) lemma, not a distinct (10).

This is a concrete payoff of the chunk decomposition: the p. 27 leaf can consume
`M1F2_step_S0_seven` (DONE) instead of re-deriving the congruence, and the
`M1-FRAG-02` boundary decision (2 steps, not 5) is what makes that citation
exact.

**`P022-R2` — the flagged "dropped factor `n`", located structurally.** The
region's first line prints

`[ n(2h^{n−3}a^n(−2n^s abck) − 2b^{n(n−3)}a^n(2n^s abck)) − 18b^{n(n−2)}(2n^s abck) ] / (6(h−b^n)^3) · (n^s abck)^3`

and its own `⇒ P₁` line immediately after prints the same term as

`− (2nh^{n−3}a^n + 2nb^{n(n−3)}a^n + 18n b^{n(n−2)}) / (3(h−b^n)^3) · (n^s abck)^4`.

The `n(...)` in the first line reaches only the first two summands: the
`18b^{n(n−2)}` sits **outside** the outer `n[...]`, while the `⇒ P₁` line writes
`18n b^{n(n−2)}`. Everything else agrees (÷6·(n^s abck)^3 with a `2n^s abck`
inside = ÷3·(n^s abck)^4 ✓). So this is the **fourth instance of the same failure
mode**: a printed factor that reaches some summands and not others, in a
computation the author re-prints one line later.

Hand-derived difference (to be confirmed numerically, not asserted): the two
readings differ by `(18 − 18n)b^{n(n−2)}/3 · (n^s abck)^4/(h−b^n)^3`, i.e.
`6(1−n)b^{n(n−2)}(n^s abck)^4/(h−b^n)^3`. Given that my hand-derived closed form
for the `7…` bracket was **falsified** by `triage_c3.py`, this one is recorded as
a hand derivation pending the same treatment — the structural observation
(which summands the outer `n` reaches) is certain from the text; the closed form
is not, until the script measures it.

**Triage of the seven flagged regions — final classification:**

| region | flag | classification |
|---|---|---|
| `P012-R1` | sign + power-of-`n` jump | **F1-adjacent**: mixed `(h−b^n)^k` / `(b^n−h)^k` denominators in adjacent terms; a presentation hazard for the transcriber, no false claim shown |
| `P014-R1` | `C₃` signs vs `P023-R1` | **candidate F4**, and p. 14 is the **outlier of four** prints (measured) |
| `P022-R2` | dropped factor `n` | **candidate F4**, located structurally above |
| `P023-R1` | `C₃` | consistent with `P023-R2` and `P024-R1` → not the suspect |
| `P024-R1` | `7…` bracket | **candidate F4** (differs from `P023-R2`, measured non-zero) |
| `P025-R1` | `2n(n−1)` vs `2(n−1)` | **candidate F4**; both prints magenta, differ by exactly a factor `n` (settled from the signed LaTeX) |
| `P027-R3` | label **(10)** carrying **(7)** | **not F4** — label reuse; content verbatim p. 6's (7), citation hazard only |

So: **four candidate F4s** (p. 14, p. 22, p. 24, p. 25) all of one failure mode,
one presentation hazard (p. 12), one label reuse (p. 27), and one region
(`P023-R1`) cleared as consistent. `P025-R1`'s "second read" is **no longer
needed** — the colour markup in the signed LaTeX answered the question that the
crop read was going to be asked, which also retires the note that colour is
absent from the region records.

### Circularity audit — instrument and result (2026-09-28, user-requested)

Anticipating a circular step in the main proof, I built a detector rather than
promising vigilance, because a literal cycle cannot reach Lean at all: imports
are acyclic and a declaration cannot reference itself, so a circularity in the
author's chain can only enter **through our transcription**, by encoding a step
with a hypothesis the print establishes only later (class F3/F4). Its signature
is therefore in the paper's *citation structure*, which is machine-checkable.

`pipeline/01-extract/cite_index.py` (host-side, read-only, 0.5 s) indexes every
printed label against every citation site from the signed region records, in
document order, and reports four anomaly classes: **FORWARD** (cited before
printed — prime suspect), **REUSED** (one label printed twice with differing
content), **ORDER** (a label re-printed below the running counter), **DANGLING**
(cited, never printed). Classification is by measured syntax: a definition is
`\quad`/`\qquad`-tagged or attached to a congruence/divisibility display; a
citation carries a Vietnamese cue (`Từ`, `theo`, `và`, `với`, `sử dụng`, `kết
hợp`, `PT`) within 16 characters. Two earlier classifier versions were wrong in
ways the evidence caught: a 60-character cue window read p. 17's *definition* of
(12) as a citation (a spurious FORWARD), and omitting `với` read p. 32's
`kết hợp với (25)` as a definition. Residual ambiguity is printed, not hidden.

**Result over the whole 33-page chain: 52 definitions, 82 citations, 37 labels —
and ZERO forward/cyclic citations.** Every citation in the document points
backward to an earlier print. What the audit found instead is the failure mode
that *mimics* circularity and is just as damaging — phantom and colliding labels
at the deepest step of the case split:

| class | finding | substance |
|---|---|---|
| DANGLING | **(26)** cited `P032-R1 L4` | **never printed anywhere.** The citation is `H(c^n,b) ≡ H(c^n,a) ≡ 0 (mod n^{s+1}) (suy ra từ (26) và (27))`. The chain runs (24), (25) on p. 31 → **no (26)** → (27) on p. 32. The display that must be (26) is printed *unlabelled* on `P031-R3 L0` (the (25)+(17)/(17') reduction), so this reads as a missing number, not missing mathematics |
| DANGLING | **(16)** cited `P032-R2 L6` | **never printed.** Used, with (28)–(32), to conclude `h − b^n ≡ a^n ≡ −b^n (mod n^s)` in the same line that correctly cites (16″). pp. 24–28 print **no** numbered labels at all (six unlabelled congruence displays), so there is no candidate display in the (16) slot |
| REUSED | **(10)** `P006-R2 L10` vs `P027-R3 L4` | the p. 27 print carries p. 6's **(7)** content under a **(10)** label — label collision, already recorded above |
| REUSED | **(25)** `P031-R2 L12` vs `P032-R1 L5` | p. 32 R1 L5 concludes `(3/2)a^{n(n−1)}(n^s abck) ≡ 0` citing "(25)"; the printed (25) is the *difference* `H(c^n,b) − H(c^n,a) ≡ 0`, and the step actually needs **(23)** (`H(c^n,b) + (3/2)a^{n(n−1)}(n^s abck) ≡ 0`) |
| REUSED (benign) | (17), (17′) `P030-R2 L0/L4` vs `L6` | adjacent-line restatement, not a collision |
| ORDER | = the three REUSED rows above | same events, other view |

**Why (26) matters more than a missing number.** From (25) one gets only
`H(c^n,b) ≡ H(c^n,a)` — *equality*, not zero. p32 R1 L4 asserts **both ≡ 0**,
and L5 then uses that (`H(c^n,b) ≡ 0` with (23)) to force
`(3/2)a^{n(n−1)}(n^s abck) ≡ 0 (mod n^{s+1})`, which yields `n = 3, vô lý` and
closes the case. So the one inference "equal to each other ⇒ both zero" lives
exactly in the slot of the never-printed (26). This is **not a cycle** — nothing
downstream feeds back into (25) or (27) — but it is a gap whose justification is
a phantom citation, at the final step before the contradiction, and it is the
single highest-risk site in the whole proof for a transcriber: filling the (26)
slot with the *desired* conclusion would assume precisely what this step proves.
Both render checks were run before drawing the conclusion (the first `(16)` is
unprimed in the image; `(26)` and `(25)` are crisp), so this is a source fact,
not a PUA/diacritic artifact.

**Cross-check at the Lean level.** The other place a circularity could enter is
our own chunk graph: a leaf that takes a *later* result (or the final theorem)
as a hypothesis. Every edge of the `depends_on` DAG points backward in the
paper's order — `L4-01←L3-01`, `L6-01←L3,L4,L5`, `M1-FRAG-01←L1-01,L6-01`,
`M1-FRAG-02←M1-FRAG-01`, and the `L7-*` leaves onto `L5-01` — and `progress.py`
rejects cycles outright. So both instruments agree: **no cycle in the author's
citations, none in our chunk graph.** The residual risk is concentrated in the
unwritten assemblies: a leaf may legitimately take the author's equation
`u^n + v^n = t^n` as a hypothesis (that is what a bổ đề does), but the assembly
must discharge it, and any hypothesis that no chunk discharges is where a
circularity would have to hide. `M1-ASM-A..E`/`M1-THM` are audited for exactly
that when written.

**Transcription-critical: the `=` line is printed in two forms that agree only as
ℤ-exponent expressions, and the ℕ encoding of one of them is FALSE.** p. 6 R2 and
p. 6 R3 both close their regrouping with the same right-hand side, written
differently:

```
p. 6 R2:  = Σ_{i=0}^{n} C_n^i a^{(n-1)(n-i)} (n^s bck)^i
p. 6 R3:  = Σ_{i=0}^{n} C_n^i a^{n(n-1-i)} (n^s abck)^i
```

The two sums are **equal — measured, not assumed**: with symbolic
`a,b,c,k,n^s = n^s`, the difference `f_R2 − f_R3 = 0` at `n = 5` and `n = 7`.
The reason is that the exponents are ℤ-valued: `n(n-1-i) = (n-1)(n-i) − i`, so
R3's summand is `a^{(n-1)(n-i)} a^{−i} (n^s abck)^i = a^{(n-1)(n-i)} (n^s bck)^i`,
and at `i = n` the exponent `−n` cancels the bracket's `a^n`.

**The trap — Lean caught it in one round (11 s), and it is OUR error, not the
author's.** Encoding R3's form with ℕ subtraction makes the last term
`a^{n·0}(n^s abck)^n = (n^s abck)^n`, wrong by a factor `a^n`; the identity
`a^{n(n-1-i)} (n^s abck)^i = (a^{n-1})^{n-i} (n^s bck)^i` is then false at
`i = n`, and `omega`'s counterexample was exactly that case. So:

* state sums that include `i = n` in the **R2 form** — it is the plain `add_pow`
  form. `M1F4_step_S1_binomial` does, so its proof needs no exponent reshaping;
* use the R3-style split only for low-order terms (`i ≤ 4`), where the print
  itself uses it and `n - 1 - i` is exact: `M1F4_absorb` carries `i + 1 ≤ n` for
  exactly this reason and its docstring records the whole story.

The `P016-R2` vs `P016-R3`/`P017-R1` flag ("exponent turnover `n(n−3)`→`n(n−2)`
with `(a^n + 2n^s abck)`"), previously a *candidate F4*, is the same convention:
re-check it under this identity before calling it a misprint, and check `i = n`
against the R2 form. It was never filed in `Q-004`, so no author time is at
stake.

**Scout findings for pp. 18–28 (crop-verify BEFORE any encoding).** Four
independent scout reports agree on one pattern: the pp. 12–28 stretch is a
single long `=`/`≡` computation in which the printed lines do *not* always
follow from one another, and the emphasis colour that would explain the moves
is not in the signed LaTeX. Flagged, with the region that needs a crop read:

| region | flagged | consequence if printed |
|---|---|---|
| `P023-R2` | coefficients contradicted by `P023-R1` **and** `P024-R1`: the `−7` bracket loses its `×7` on `h^{n−1} − b^{n(n−1)}`, and `6b^{n(n−2)}` loses its `n` | a **false** printed line; would be F4 → author query |
| `P025-R1` d4 vs `P026-R2` d4 | `2n(n−1)` becomes `2(n−1)`: a bare factor `n` vanishes, and the difference is only `n^{4s}`, not `n^{4s+2}`, so no mod-`n^{4s+2}` reduction absorbs it | candidate F4 |
| `P016-R2` vs `P016-R3`/`P017-R1` | exponent turns over `n(n−3)` → `n(n−2)` and an `(a^n+2n^s abck)` factor appears/disappears | which form is authoritative must be read off the crop |
| `P012-R1` → `P012-R2` | a term re-enters as `+n²[…]/(b^n−h)²` where R1 printed `−[…](h−b^n)/(h−b^n)³` (sign **and** power of `n` jump) | transcribe each region's own form; classify, never bridge |
| `P023-R1` `C₃` vs `P014-R1` | `h^{n−2}` and `b^{n(n−2)}` coefficient signs flipped | F1/F4 decision needs the crop |
| `P022-R2` | drops a factor `n` on `−18b^{n(n−2)}(2n^s abck)` vs its own final `P₁` line | idem |
| `P027-R3` | a congruence printed with label **(10)** whose content is **(7)**'s (`mod n^{2s+1}`, not `n^{5s+1}`); the label digits carry no colour | label vs content must be crop-decided |
| `P026-R1` | leading arrow glyph read as a **left** double arrow where `P025-R2` has a right one | decides the chain direction |
| `P016-R2` | one exponent digit is a private-use glyph `U+F032` (`n(n−2)`) | crop confirms the digit |

**Crop verification — first results (2026-09-28, four crops read).**

| region | crop read | outcome |
|---|---|---|
| `P023-R2` | `page-023-300dpi-region-02.png` | **Two independent oddities confirmed.** The crop's numerator reads `7b^{n(n−4)}(b^n−h)³ + 7b^{n(n−3)}(b^n−h)² − 7b^{n(n−2)}(h−b^n) + h^{n−1} − b^{n(n−1)}` — the `7` sits on the first three summands only, so `h^{n−1} − b^{n(n−1)}` enters with coefficient `1` where `P023-R1` and `P024-R1` print `7(h^{n−1} − b^{n(n−1)})`. The crop likewise confirms `6b^{n(n−2)}` (no factor `n`) inside the `5[…]` bracket. The crop therefore **agrees with the signed LaTeX** — the inconsistency is between printed regions, not in our transcription. |
| `P026-R2` | `page-026-300dpi-region-02.png` | Confirmed as signed: the magenta fraction is `2(n−1)[b^{n(n−2)}+a^{n(n−2)}−h^{n−2}](n^s abck)⁴/(h−b^n)³` (coefficient `2(n−1)`, **no** `n`), the `a^{n(n−3)}` coefficient is `2n`, and `−2n a^{n(n−3)}(a^n+2n^s abck)(n^s abck)⁴/(h−b^n)³` **is** printed in red in this region. So the `(a^n+2n^s abck)` factor is not a transcription error at P026-R2 — the turnover happens between `P016-R3`/`P017-R1` and here. |
| `P025-R1` | `page-025-300dpi-region-01.png` | **Not resolved.** The crop carries no `(d0)…(d4)` sub-labels (the scout's labels are its own reading of the sequence, not printed tags), and the vision report answered both ways on which coefficient is magenta: it places the blue coefficient `n(n−1)(n−2)` on the `a^{n(n−3)}` term and the `2(n−1)`/`2n(n−1)` pair on the `a^{n(n−2)}` fraction. A second read of `P025-R1` **together with** `P024-R1` (same expression, previous page) is required before `M1-FRAG-32` is written. |
| `P016-R2` | `page-016-300dpi-region-02.png` | Confirmed: the exponent is `n(n−2)` (the PUA glyph is a `2`), `(a^n+2n^s abck)` is **absent** from `2n²a^{n(n−2)}(n^s abck)³`, and the red negative term `−2n a^{n(n−3)}(a^n+2n^s abck)(n^s abck)⁴/(h−b^n)³` is present in that same region. So both spellings the scout flagged coexist on the page. |

Reading rule this establishes for the lane: **a coefficient that differs between
two printed regions is settled by the crops only when the crops disagree with the
signed LaTeX.** Here they agree, so the two `P023-R2` oddities and the
`2n(n−1)`/`2(n−1)` turnover are *printed* discrepancies. Per AGENTS.md the next
step is not to bridge them: read the two neighbouring regions' crops (P023-R1,
P024-R1, and for the coefficient P025-R1 + P024-R1); if the neighbouring prints
carry the `7`/the `n`, the conclusion is that the *odd* region is a printed slip
and the chunk that touches it is **F4 → author query** (the (27) cancellation and
the F-chain are downstream of these lines). Five crops of the nine still to read:
`P012-R1/R2`, `P014-R1`, `P022-R2`, `P023-R1`, `P024-R1`, `P025-R1` (second read),
`P027-R3`.

**Scout findings from pp. 6–11 and 29–33 (beyond §5's table).**

- pp. 6–11: `P008-R1/R2/R3` re-print the same `≡ F (mod n^{4s+2})` closure three
  times — leaves 07/08 split one continuous computation; a duplicate print is not
  a second proof step and must not be counted twice (`M1-FRAG-08` should be
  verified as a restatement, not re-derived).
- pp. 6–11: sign ambiguities needing a crop before any statement — `P009-R1/R3`
  has a double minus inside `M`'s first definition; `P007-R1`'s residual
  condition `l + j ≥ 5` and the `(−1)^j` exponent had *vision disagreement* (my
  own screen of the same region passed the `l+j ≥ 5` reading, and it is the only
  reading under which the residual is non-vacuous — §7 item 1).
- pp. 29–33: the loose ends of the whole proof, all four now pinned with regions —
  **(i)** `P032-R1`'s cancellation is the one step that must be *proved*, and its
  printed "vì" clause is an assertion whose factor list differs from bổ đề 7's
  product, with `¬n ∣ a^n + b^n` never printed (it needs `a^n + b^n ≡ c^n
  (mod n^s)`); **(ii)** labels **(16)** (cited at P032-R2) and **(26)** (cited at
  P032-R1) are **defined nowhere in pp. 1–33** — crop-verified; **(iii)**
  `P033-R1` prints `55/3` while its own fourteen listed coefficients sum to
  `55/4` (denominator glyph ambiguous); **(iv)** Mathlib has no FLT for `n = 5,
  7, 11` (only `Three.lean`/`Four.lean`), so §2's Dirichlet/Lamé/Kummer lines
  must be explicit **hypotheses** of `M1-ASM-E` — never axioms, since
  `#print axioms` permits only propext/Classical.choice/Quot.sound.
- The final assembly home is `P033-R2` ("Vậy định lý lớn Fermat đã được chứng
  minh") — `M1-FRAG-41` / `M1-THM`.

**Technical constraint confirmed twice (pp. 18–28) — do not formalize the
printed fractions literally in ℤ.** The work modulus is `n^{4s+2}`, which is
composite, so `ZMod (n^{4s+2})` has **no `Field` instance** and `field_simp` is
unavailable there; the "Quy ước" of `P009-R2` (`m(h−b^n)^r ≢ 0 (mod n)`) is what
licenses the printed divisions. Two viable routes: (a) prove the identities over
`ℚ`/`ℤ` first and transfer, or (b) state them denominator-cleared and cancel with
`IsCoprime` / `isUnit` facts (candidate: `ZMod.isUnit_natCast_iff_not_dvd_pow`,
verify by `#check` before use). Either way each printed line must be classified
`=` vs `≡ (mod n^{4s+2})` individually — the long `= P₁ =` chain is not a chain
of equalities.

## 8. Session report (2026-09-28, 2-hour window)

Window: open 02:58:47Z, close 04:58:47Z (epoch 1790564327 + 7200); **extended by
the user at 04:11Z to a close of 06:11Z** — the extension's work is recorded
below. Gates at
open: `check_env.sh` SMOKE PASS, `progress.py --check` exit 0 with 13/13 DONE,
0 open obstacles/queries. Gates at close: `progress.py --check` **exit 0**,
13/14 DONE (`B-01` TODO, 0 BLOCKED), watchdog live, one compile round spent.

### What was built (every file kept)

| artifact | role |
|---|---|
| `proof/watch_lane.sh` → `M1_watch.log` | mechanical watchdog, running as service `watch-m1`: 60 s heartbeat (container, lean/lake process count, in-flight age, newest-log age), one latch per episode — `ENV-DOWN`, `CONTENTION`, `STALL` (>900 s with 0 lean processes), `OVERRUN` (>1500 s), `DISK` |
| `proof/run_round.sh` | one compile round: in-flight handshake → container-side log → handshake removal → ledger row. Removes the four hand-rolled steps where this repo has lost evidence before |
| `pipeline/03-lean/M1_LANE.md` | lane state: §1 round protocol, §2 wall-clock reporting, §3 circuit breakers, §4 observer protocol, §5 chunk plan, §6 artifacts, §7 findings, §8 this report |
| `pipeline/03-lean/M1_rounds.tsv` | round ledger (round, chunk, step, file, start, dur, exit, errors, class, diagnosis) |
| `pipeline/03-lean/M1_scout/pp06-11.md`, `pp12-17.md`, `pp18-23.md`, `pp24-28.md`, `pp29-33.md` | region-level inventories of pp. 6–33 (25+19+19+18+14 regions; six read-only scouts, no container use) |
| `pipeline/03-lean/probes/M1-LANE.probe.lean` + `.names.tsv` | 51-name batched probe in 5 clusters; 50 rg-confirmed against the pinned tree, 1 (`Nat.pow_dvd_pow_iff_le_right`) unverifiable by grep because it is toolchain-provided — it is already *called* by the DONE chunks L4/L6 |
| `pipeline/04-sympy/m1_common.py` | shared screens: vacuity accounting, the §1.1 expansion core, the tail truncations, the p. 6 regrouping, p. 7 R1's RHS, section B |
| `pipeline/04-sympy/test_b_01.py` | chunk-level screen entry point for `B-01` (joins `run_all.py`) |
| `pipeline/02-chunks/chunks/B-01.yml` + `status.tsv` row | the missing prerequisite chunk; `source_text` byte-copied from the signed record, crop read recorded in `renders` |

### Numeric results — `python m1_common.py` PASS, EXIT 0

- **Vacuity, stated honestly:** `x^n + y^n = z^n` has 0 solutions for
  `n ∈ {3,5,7}` (coords ≤ 40). The main proof's outer hypotheses are therefore
  unsatisfiable, so everything *conditional on (3)* must be verified in Lean,
  not screened.
- **Expansion identity**, exact (no modulus) at n = 5, 7, 11, 13, 17, 19, 23.
- **Tail truncations** for orders 0–4 at those seven primes, 6 instances each,
  printed moduli **sharp** — this is the unconditional content of (7)/(7′)/(8)/
  (9)/(10) (see the F1 in §7).
- **p. 6 triple-sum regrouping:** all 10 printed index ranges are the natural
  `[l, n−1−j]`, the `l+j` partition is exact, residual non-vacuous (19/161/300
  summands at n = 7/11/13). p. 7 R1's 5 continuation groups match exactly the
  remainder the p. 6 page does not print.
- **p. 7 R1 RHS:** printed `i ≤ 4` terms + tail `= (a^{n−1} + n^s bck)^n`.
- **Section B:** `B.1` on 50 random instances; `B.2`'s middle form as the same
  sum read backwards and its last form confirmed by exact symbolic
  differentiation (`m ≤ 7`, `k ≤ 4`).

### Problems found, by impact

1. **The main proof depends on unverified auxiliary results.** Printed
   `B. MỘT CÁCH BIẾN ĐỔI TỔNG Σ₃ …` sits in `P002-R1` and is cited as
   `mục B.1`/`mục B.2, trang 2` at 11 sites from p. 9 on (P009-R3, P010-R1,
   P011-R4–R9, P013, P014). **No DONE chunk covers it** — `L1-01`…`L7-ASM`
   verify section C (lemmas 1–7) on the same page and after. Found twice
   independently (my section-map grep and the pp. 6–11 scout's `PREREQ-p2B`).
   Fixed: chunk `B-01` written, screened, crop-read; `B-01` is TODO and is now
   the dependency of leaves 11, 15, 16, 18, 19, 20 and the cited `B.1/B.2`
   users in pp. 12–14.
2. **Printed coefficient inconsistencies — candidate F4s that must be settled
   by crops before their leaves are encoded** (details and regions in §7):
   `P023-R2` (two independent oddities, crop-confirmed as printed),
   `P025-R1`/`P026-R2` (`2n(n−1)` vs `2(n−1)`, difference `n^{4s}`, not
   absorbable), `P016-R2` vs `P016-R3`/`P017-R1` (exponent turnover
   `n(n−3)`→`n(n−2)` plus the `(a^n+2n^s abck)` factor), `P012-R1`→`R2`
   (sign **and** power-of-`n` jump), `P022-R2` (dropped factor `n`),
   `P023-R1` `C₃` (sign flips vs `P014-R1`), `P027-R3` (label **(10)** carrying
   **(7)**'s content), `P026-R1` (arrow direction, left vs right).
3. **Two labels are cited but defined nowhere in pp. 1–33:** **(16)** (at
   `P032-R2`) and **(26)** (at `P032-R1`) — crop-verified. Plus `P033-R1` prints
   `55/3` where its own fourteen coefficients sum to `55/4`.
4. **The (27) cancellation at `P032-R1` is the one step that must be proved**,
   and its printed "vì" clause is an assertion whose factor list differs from
   bổ đề 7's product; `¬n ∣ a^n + b^n` is never printed (it needs
   `a^n + b^n ≡ c^n (mod n^s)`). This is the deepest substantive risk in the
   whole lane and it sits on the critical path of §1.2.
5. **Colour carries algebra on pp. 12–28 and is not in the signed LaTeX** — the
   region records encode `\textbf` for headings only. 4 of the 9 flagged crops
   are read (results in §7); 5 remain (`P012-R1/R2`, `P014-R1`, `P022-R2`,
   `P023-R1`, `P024-R1`, `P025-R1` second read, `P027-R3`). Until they are read,
   those leaves cannot be faithfully transcribed.
6. **`ZMod (n^{4s+2})` has no `Field` instance** (composite modulus), so
   `field_simp` is unavailable and the printed divisions rest on the `P009-R2`
   "Quy ước". Formalize denominator-cleared, or cancel with `IsCoprime`/units;
   and classify every printed line `=` vs `≡ (mod n^{4s+2})` individually — the
   long `= P₁ =` chain is not a chain of equalities.
7. **Mathlib has no FLT for `n = 5, 7, 11`** (only `Three.lean`/`Four.lean`), so
   §2's Dirichlet/Lamé/Kummer lines must be explicit **hypotheses** of
   `M1-ASM-E` — never axioms (`#print axioms` allows only propext,
   `Classical.choice`, `Quot.sound`).
8. **Scale:** 41 leaves + 1 prerequisite + 6 assemblies ≈ **250–400 container
   rounds ≈ 20–35 h**. The 2-hour window necessarily covers planning, the
   prerequisite chunk, and the numeric screens only — no main-proof leaf was
   encoded, so there is no S1 on the main proof yet.
9. **Tooling notes for the next session** (each cost time here):
   `progress.py --write` is cwd-dependent — the container's cwd is
   `/workspace/work`, so it must be given the **absolute** path
   `/workspace/pipeline/PROGRESS.md` or it writes a stray file into the work
   volume; `docker compose exec` from the `bash` tool works but long commands get
   backgrounded by the harness; the `read` tool truncates region `latex` lines at
   768 chars so long displays need `sed`/`fold` on the host; **hand-typed
   Vietnamese literals in scripts do not match the file's bytes** (the
   documented diacritic-corruption path) — anchor text extraction on ASCII
   fragments such as `\textbf{B.`; and **MSYS/Git-bash mangles a leading-slash
   argument** (`/workspace/proof/compile_lean.sh` becomes
   `C:/Program Files/Git/workspace/...`, exit 2 in 0 s) — `proof/run_round.sh`
   now exports `MSYS_NO_PATHCONV=1`, and the pitfall is appended to
   `AGENTS.md`'s tooling list. One round was burned on it before the fix.

### Lane mechanics exercised end to end

- **Watchdog** (`proof/watch_lane.sh`, service `watch-m1`) ran the whole
  window: 26 heartbeats, 2 latches, both diagnosed and ACKed in `M1_watch.log`.
  `ACK 1` — false positive: one `lake env lean` legitimately appears as a *pair*
  of processes (`lake` + `lean`), so the old `proc > 1` test flagged every
  round; the counter now counts `lake` separately (patched 03:24Z). `ACK 2` —
  **true** positive: two compile rounds ran concurrently (my own diagnostic
  overlapping the harness round), exactly the contention whose cost this repo
  measured at 3× earlier.
- **Round harness** `proof/run_round.sh` produced the in-flight handshake, the
  container-side log, and the ledger rows.
- **Round 1 (probe) — S1:** `exit=0`, `355 s`, `error_lines=0`. All 51
  `#check` lines elaborate, so every name in the five clusters exists as written
  at this pin; 63 signature lines in the log, archived as
  `probes/M1-LANE.probe.log`, header flipped to VERIFIED. That closes the
  probe's one unverifiable-by-grep row (`Nat.pow_dvd_pow_iff_le_right`, which is
  toolchain-provided and therefore has no declaration site to grep).
- **Round 0** is the failed attempt, classed **ENV** (not F1–F4): Git-bash had
  converted the container path to `C:/Program Files/Git/…` and Lean never
  started. Cost: one round attempt.
- **No main-proof author step has been encoded**, so the window's only S1 is the
  probe. Every leaf of §5 is still TODO.

### The ABI sheet (`SIGNATURES.md` + `gen_signatures.py`) — adopted late

Did this lane use it? **No, and it should have.** Measured:

- `M1_LANE.md` referenced `SIGNATURES.md` **zero** times, although AGENTS.md
  makes reading it mandatory before Lean work. The sheet and its pin log were
  fresh (02:18–02:19Z; no `Basic.lean` newer than the log), so it was
  trustworthy for the whole window and simply went unread.
- The two probe layers are **disjoint**: 0 of the 51 names in
  `probes/M1-LANE.probe.names.tsv` occur among the 118 generated `#check` lines.
  The generated probe covers **project** declarations — the ones that have a
  call-site shape to get wrong — while the hand-written M1 probe covers
  **Mathlib** names. Neither substitutes for the other; the earlier idea of
  "deduping" them was wrong.
- §1's before-a-round gate now requires the producer-header read (coordinate,
  modulus, form, orientation). For M1 the live traps are the printed modulus
  ladder `n` / `n²` / `n^{4s+2}` and `≡` vs `- ≡ 0` vs `∣` — and the L7 lane's
  own record is that *every* one of its error rounds came from exactly that.
  Against a 250–400 s round, the header read is free.

**Bug found in the generator while wiring section B into it (fixed).** Adding
`("B", …)` to `MODULES` exposed an asymmetry: the sheet body and the module
inventory skip a module whose `Basic.lean` does not exist yet, but the probe's
*imports* did not — the regeneration emitted `import B.Basic` for the
not-yet-written `B-01` chunk, which would have made the whole 119-line probe
fail to elaborate and taken every other pinned name down with it. The import
list is now guarded identically. Verified: with the guard both generated files
are byte-identical to their pre-change state (`SIGNATURES.md` `e8479ea2fcd5c3fd`,
probe `36c8a5cefa4de9ee`) while `B` stays registered — so `B-01` appears in the
sheet automatically at its DONE flip — and `ENTRY` now also recognises
`B_rules` as a citeable entry point.

### Window extension (04:11Z → 06:11Z): the first main-proof leaf is DONE

Every round the lane has spent, with its outcome — the whole cost record:

| round | target | result |
|---|---|---|
| 0 | probe `M1-LANE.probe.lean` | **ENV**: MSYS/Git-bash mangled the container path (`C:/Program Files/Git/…`), exit 2 in 0 s, Lean never started. Fixed in `run_round.sh` (+ AGENTS.md) |
| 1 | probe, re-run | **S1** EXIT 0, 355 s, 0 errors — all 51 `#check` names elaborate at this pin |
| 2 | `M1F1` (S3) | **ENV**: killed by the harness's 300 s default deadline mid-compile (needed ~320 s); empty log, stale handshake cleared. `async` does *not* extend the deadline |
| 3 | `M1F1` S0+S1+S3+S4 | **F2** (1 error + 1 warning, both in the *probe* block: `Nat.Prime.prime_int` does not exist, and a linter unused-variable) — **all four declarations elaborated anyway** |
| 4 | same + `#print axioms` | **S1** EXIT 0, 341 s, 0 errors, 0 warnings, 0 `sorry`; axioms `[propext, Classical.choice, Quot.sound]` for all four |
| 5 | `B-01` B.1 + B.2-first | **F2** syntax: `∑ i in …` (ASCII binder) does not parse at this pin. All 8 pinned names exist |
| 6 | same, `∈` fixed | **F2** tactic: `omega` cannot prove the raw `Icc`-form range equality `(n+1)-k = (n+m-k+1)-m` (truncated subtraction is not linear — it reports a spurious counterexample), and `sum_range_reflect` wants the reverse direction |
| 7 | same, `congr 1` added | **F2** tactic: two rewrites were the right idea at the wrong nesting level — Lean had already simplified the reflected index |
| 8 | B.1 in range form + B.2-first | **F2** tactic: after the `descFactorial` and `x`-exponent rewrites landed, only the `h` exponent `m-1-(m-1-i) = i` was left |
| 9 | same | **S1** EXIT 0, 362 s, 0 errors, 2 warnings (`_hkm` since fixed) — **B.1 and B.2's first equality verified** |
| 10 | `M1F2` support lemmas | **F2**: 5 mechanical errors (`subst` eliminated `n`; `dvd_mul_of_dvd_right` with the factor on the left; `pow_add` in the other exponent order; and a `show n = (n-1)+1` rewrite that replaced **every** `n` in the goal) |
| 11 | same, all four fixed | **F2**: 2 one-liners — a `norm_num` ran on an already-closed goal, and the exponent needed `← pow_add` |
| 12 | same | **F2**: 1 error, and a useful one — `← pow_add` still could not match because the `Q` sits *inside* the right factor (`a^(2s+1) * (a^(j-(2s+1)) * Q)`), so `← mul_assoc` has to reassociate before `pow_add` can fire |
| 13 | same | **S1** EXIT 0, 361 s, 0 errors — `M1F2`'s support verifies: the ZMod↔ℤ bridge, the exponent helper, the **tail-vanishing lemma** (`n^(2s+1) ∣ C(n,i)·(n^s Q)^i` for `2 ≤ i ≤ n`) and the truncated-expansion lemma `M1F2_expand_trunc` |
| 14 | `M1F2` S0 + S1 + axioms | **F2**: all three expansions rewrote into `hsol` correctly, but `linarith` saw `(a^n)^n` and `a^(n^2)` as *different atoms*; a `pow_add` that cannot fire while `Q` sits inside the right factor; and `Int.ModEq.zero_iff_dvd` is really `Int.modEq_zero_iff_dvd` (lower-case `modEq`) |
| 15 | same | **F2**: 2 errors, one character each — at this pin `pow_mul` is `a^(m*n) = (a^m)^n`, so the goal needs `rw [← pow_mul]` |
| 16 | same | **S1** EXIT 0, 352 s, 0 errors, 0 warnings, 0 `sorry`; axioms `[propext, Classical.choice, Quot.sound]`. **`M1-FRAG-02` DONE** |

**`M1-FRAG-01` is DONE** — the first main-proof chunk. Its five printed steps
became four declarations, because S2 is the author's WLOG choice and not a
claim: it is carried as the two hypotheses `hnu`, `hnv` of S3, exactly as the
print carries it as an assumption.

* `M1F1_step_S0_reduce` — bổ đề 1 at the lane's hypothesis (`L1_bo_de_1`);
* `M1F1_step_S1_symmetry` — the four printed forms under `Odd n`, via
  `Odd.neg_pow` and `linarith`;
* `M1F1_step_S3_bo_de_6` — bổ đề 6 read at this instance; `n ∤ u*v` is *derived*
  from the two non-divisibilities through
  `Int.prime_iff_natAbs_prime.mpr` + `Prime.dvd_mul`, which is the only place the
  step adds anything to the DONE entry point;
* `M1F1_step_S4_substitute` — S3's four identities substituted into (3).

`progress.py --check` exit 0, **14/16 DONE**, with `B-01` and `M1-FRAG-02` the
two TODOs (no BLOCKED, no open obstacles or author queries).

**`B-01` — 2 of its 3 steps verified.** `B_step_S0_index_shift` (B.1) and
`B_step_S1_reindex` (B.2's first equality) are S1 as of round 9 (EXIT 0, 362 s,
0 errors). B.2's second equality — the falling-factorial sum *is* `f^{(k)}(x)` —
is the one step still unwritten, and its whole recipe is now pinned in the chunk
record: `Polynomial.iterate_derivative_sum`, `iterate_derivative_C_mul`,
`iterate_derivative_X_pow_eq_smul` (`derivative^[k] (X^n) = (n.descFactorial k) • X^(n-k)`),
`eval_finsetSum`, then the re-indexing `i = m-1-t` with the terms `t > m-1-k`
vanishing because `Nat.descFactorial_eq_zero_iff_lt`. All five names were
verified against the pinned source, so that step is an encoding exercise, not a
search. The chunk stays TODO: `progress.py` would not accept a DONE flip with a
step missing.

**Evidence integrity note.** `B/Basic.lean` was edited *after* its round 9
compile — the load-bearing-but-proof-unused hypothesis `k ≤ m-1` was renamed
`hkm` → `_hkm` to clear a linter warning. The current file text is therefore
**not** the text round 9 certified. Nothing on disk claims otherwise (`B-01` is
TODO, not DONE), but the next round on this file must be treated as the
certifying one: it has to add B.2's second equality anyway, and its
`#print axioms` output is what the DONE flip will rest on.

**B.1 is encoded in the range form both sides share.** The literal `Icc` form is
what the print shows, but its range equality `(n+1)-k = (n+m-k+1)-m` is *true*
in ℕ and **`omega` rejects it** with a spurious counterexample, because truncated
subtraction is not linear; that would have forced a hand-rolled case split whose
entire content is ℕ bookkeeping. The range form is also what the main proof
consumes (it cites B.1 to re-index range sums in pp. 12–14), and the decision is
recorded in the chunk record as well as here.

**`M1-FRAG-02` is DONE** (round 16: EXIT 0, 352 s, 0 errors, 0 warnings, 0
`sorry`; axioms `[propext, Classical.choice, Quot.sound]`). Rounds 10–15 got it
there. The leaf's support proves the point the print only asserts — that the tail
of the expansion is divisible by the printed modulus — with `n^(2s+1) ∣
C(n,i)·(n^s Q)^i` for `2 ≤ i ≤ n` split into `i = n` (`C(n,n) = 1`, exponent
`s·n ≥ 2s+1`) and `2 ≤ i ≤ n-1` (`n ∣ C(n,i)` supplies the decisive factor), on
top of `M1F2_expand_trunc`. `M1F2_step_S0_seven` is then the printed (7) and
`M1F2_step_S1_seven_prime` its companion (7′), whose content is a one-line
consequence of (7) that the print nonetheless labels separately.
The support lemmas — the ZMod↔ℤ bridge, the exponent
helper, the **tail-vanishing lemma** (`n^(2s+1) ∣ C(n,i)·(n^s Q)^i` for
`2 ≤ i ≤ n` — the mathematical content of (7)) and `M1F2_expand_trunc`, all S1 at
round 13 (EXIT 0, 361 s, 0 errors). The two labelled steps `M1F2_step_S0_seven`
and `M1F2_step_S1_seven_prime` are written and were down to **two one-character
errors** at round 15: at this pin `pow_mul` is `a^(m*n) = (a^m)^n`, so the goal
needs `rw [← pow_mul]`. That fix is applied in the file and **not yet
re-compiled** — it is the next session's first round, and it should be a
one-round S1 with the `#print axioms` evidence already in place.
The leaf is the printed (7) and (7′), and both are *congruences of the
expansion*, so its support has to establish that the tail vanishes: for a prime
`n`, `n^(2s+1) ∣ C(n,i) · (n^s Q)^i` for every `2 ≤ i ≤ n`, which splits into
`i = n` (where `C(n,n) = 1` and the exponent `s·n` is already large enough) and
`2 ≤ i ≤ n-1` (where `n ∣ C(n,i)` supplies the decisive factor `n`). That lemma,
the exponent helper, the ZMod↔ℤ bridge and the truncated-expansion lemma are in
`03-lean/M1F2/Basic.lean`. Rounds 10–12 were spent on them and every error was
mechanical, not mathematical — the leaf's *statement* has been numerically
screened since the first window (`m1_common.screen_tail` checks exactly this
tail divisibility for orders 0–4 at `n ∈ {5,7,11,13,17,19,23}`, PASS).

**Triage of the flagged regions, by measurement instead of by eye.** Two
cross-print inconsistencies are now numbers rather than readings (§7): `C₃` at
`P014-R1` differs from the three other prints of the same quantity by
`10n(h^{n−2} − b^{n(n−2)})`, which makes **p. 14 the outlier of four prints**,
and the `7…` numerator at `P023-R2` differs from `P024-R1` by a non-zero
polynomial. Both are one failure mode — a printed factor that fails to
distribute over a bracket — and both are the kind of finding that should reach
the author once. One of my own hand-derived closed forms was **falsified** by the
check and is recorded as falsified rather than quietly dropped.
`04-sympy/triage_c3.py` EXIT 0.

**Adopted late, and it cost real time: the ABI sheet.** `SIGNATURES.md` +
`gen_signatures.py` went unreferenced by this lane until 04:11Z even though
AGENTS.md makes reading them mandatory and they were fresh. The two probe layers
are **disjoint** (0 of 51 names overlap), so both are kept; the generator's
`MODULES` now also knows `B` and `M1F1`, and a latent bug in it was found and
fixed (its `import` list did not skip unwritten modules, unlike its body).

### Closing state

- **Ledger:** 16 chunks — **15 DONE** (13 pre-existing + `M1-FRAG-01` + `M1-FRAG-02`),
  1 TODO (`B-01`, with 2 of its 3 steps already S1), 0 BLOCKED, 0 open obstacles,
  0 open author queries. `progress.py --check` exit 0; `PROGRESS.md` regenerated.
- **Rounds:** 17 in the extension — **5 S1, 2 ENV, 10 F2**. The two ENV rounds
  were tooling losses (MSYS path mangling; the harness deadline), and the F2
  rounds were notation/API/index work, with **no mathematical rejection of any
  printed step**. Every round's class and diagnosis is in `M1_rounds.tsv`; that
  table is the cost record this lane was built to produce: **5 S1, 2 ENV, 10 F2**
  is the number any proposal for "better documentation" should be measured
  against, and it is why the recommendation made in this session's answer was
  about the *feedback loop* (persistent elaboration) rather than more prose.
- **No author query was filed**, deliberately: the **four** measured cross-print
  inconsistencies (the `C₃` at `P014-R1` vs its three consistent re-prints; the
  `7…` bracket at `P023-R2` vs `P024-R1`; the magenta coefficient at `P025-R1`
  vs `P026-R2`; the dropped `n` at `P022-R2`) are all one failure mode — a
  printed factor that reaches some summands and not others — and they belong to
  leaves on pp. 14 and 22–26. The questions to ask are sharper once the
  intervening derivations (p. 13, pp. 21–22) are transcribed, so the findings are
  recorded with their measurements and the query is to be written in one pass.
  The seventh flag (`P027-R3`) is **not** F4: it is a label reuse, and the sixth
  (`P012-R1`) is a denominator-presentation hazard, not a false claim.
- **The strongest result of the window is a negative one, stated precisely:** the
  printed (7)–(10) are *not* identities. They hold only under `u^n + v^n = t^n`,
  and their unconditional content is exactly the tail divisibility
  `n^((order+1)s+1) ∣ Σ_{i>order}(…)`. That is now both screened numerically
  (`screen_tail`, orders 0–4) and proved in Lean for order 1 (`M1F2`'s
  tail-vanishing lemma), which is what makes the leaf encoding faithful rather
  than convenient.
- **Files added in the extension:** `03-lean/M1F1/Basic.lean` (DONE),
  `03-lean/M1F2/Basic.lean`, `03-lean/B/Basic.lean`, `02-chunks/chunks/M1-FRAG-01.yml`
  (DONE), `02-chunks/chunks/M1-FRAG-02.yml`, `04-sympy/triage_c3.py`; plus
  `lakefile.toml` wiring for `B`, `M1F1`, `M1F2` and `gen_signatures.py`
  registration of all three.

### Next session, in order

1. Finish the crop pass (5 crops, §7) and classify each flagged region F1 or F4;
   if F4, file the author query **before** any downstream leaf is stated.
2. Encode `B-01` (3 steps; its probe round is already spent) and flip it DONE.
3. Encode leaves `M1-FRAG-01`–`03` (pp. 6–7), whose algebra is already
   screen-verified, then 04–06.
4. Keep §3's breakers binding: at ≥3 failed rounds on one step, hand the
   evidence packet to the observer before another attempt.

### Update — thirteenth session (2026-09-28, later): `M1-FRAG-03` DONE (17/17→17/18), `M1-FRAG-04` in flight

- **Ledger:** `M1-FRAG-03` is DONE (rounds 27 + 28, EXIT 0, no warnings,
  `propext`/`Classical.choice`/`Quot.sound` only, no `sorryAx`). `M1-FRAG-04`
  (pp. 6–7) now has its **own `status.tsv` row (IN_PROGRESS)** — the chunk file
  had existed without one, which `progress.py --check` reports as an
  inconsistency; the dashboard had been quoted without its exit code, so it went
  unnoticed. `progress.py --check` now exits 0 with **17/18 DONE, M1-FRAG-04
  IN_PROGRESS**; the watchdog is live (`latched=none`).
- **`M1-FRAG-04` state (rounds 34–37):** S0 (`M1F4_step_S0_triple`) and S1
  (`M1F4_step_S1_binomial`) certified, on `M1F4_add_pow_neg` and `M1F4_absorb`.
  Round 36 landed the first half of S2 as `M1F4_sum_complement` — the pointwise
  filter complement behind the printed `l+j ≥ 5` split, stated for an arbitrary
  summand so it is about the index structure only; round 37 certificated all
  three (EXIT 0, 0 warnings, permitted axioms only).
- **S2 frozen — and a correction to this report's own earlier count.** The
  printed boundary display is **one sum for each pair `(j,l)` with `j+l ≤ 4`:
  FIFTEEN** (`C(6,2) = 15`), not the ten §7's numeric screen note guessed; and
  **every printed range is exactly the natural `i ∈ [l, n-1-j]`** with the triple
  sum's own summand. So that display carries **no misprint** — a positive result,
  and it confirms the screen's "partition exact" at representation level. The
  remaining half of S2 is the **`(j,l,i)` re-indexing** (the two index sets are
  the same set in a different order); its statement, its bijection obligations
  and the recommended `Finset.sigma` + `Finset.ext` + `omega` route are in
  `M1-FRAG-04.yml`. Estimated 40–80 lines, several rounds — the leaf's most
  expensive step, and the current edge.
- **S2 landed and certified (rounds 39-41).** `M1F4_reindex` — the `(j,l,i)`
  re-indexing, i.e. the leaf's hardest step — took two rounds: one genuine F2
  (`rw [← hR]` where `hR` rewrites the printed nested sum *into* the σ-sum, so the
  pattern was absent), then EXIT 0, 9 s, zero errors, zero warnings. Route that
  worked: flatten both sides with `simp only [Finset.sum_sigma']` to one sum over
  a Finset of nested σ-pairs, keep `l+j ≤ 4` as a `Finset.filter` (`←
  Finset.sum_filter`), and identify the two filtered index sets with
  `Finset.sum_nbij'` along `⟨i,⟨j,l⟩⟩ ↦ ⟨j,⟨l,i⟩⟩` — the arithmetic obligations
  are four linear Nat facts and `omega` closed them directly (even with the
  truncated `n - i` / `5 - j` forms). The composed author step is
  `M1F4_step_S2_split` (the complement plus the re-indexing plus the pointwise
  `¬(5 ≤ j+l) ↔ j+l ≤ 4` bridge); all five declarations carry `propext`,
  `Classical.choice`, `Quot.sound` only, no `sorryAx`.
- **Step-map correction (F1-class, ours not the author's): the printed display's
  real step order differs from this lane's earlier plan.** Verbatim line dump
  (2026-09-28): `P007-R1` runs to **l12**, and its `l4-l6` is a *separate step*
  (the RHS tail `Σ_{i=5}^{n} C_n^i a^{(n-1)(n-i)} (n^s bck)^i` plus the four
  explicit terms) that precedes the factorial forms; the factorial forms printed
  inside this chunk's regions are only the **five X⁴ sums** (R1 l8-l12), and that
  display **continues past the page break** into R2/R3. So `M1-FRAG-05/06`'s
  boundaries — recorded from *estimated* line numbers — must be re-aligned to the
  real region line counts before those leaves are written. `M1-FRAG-04`'s S3/S4
  are now specified in `M1-FRAG-04.yml` with that correction, including the
  ℕ-safety constraint on S3 (any range containing `i = n` must use the absorbed
  `a^{(n-1)(n-i)}(n^s bck)^i` form).
- **`M1-FRAG-04` is DONE — the ledger is 18/18 (100%)** (round 55 certificate:
  EXIT 0, 0 warnings, permitted axioms only on all 16 declarations, no `sorryAx`).
  S3 (`M1F4_step_S3_tail`) is the author's RHS rewrite — the split of `Σ_{i=0}^{n}`
  at 5 plus per-term absorption (`Finset.sum_range_add_sum_Ico` + `M1F4_absorb`),
  with `hn : 5 ≤ n` as the F3 side condition the paper leaves implicit. S4
  (`M1F4_step_S4_factorial`) is the five `X^4` boundary sums in the printed
  factorial form, via four `Nat.choose`-to-falling-factorial bridges plus three
  `_shift` forms stated in the author's own `(n-2-i)` shape.
- **What S4 cost, and why it is in the lessons file.** S3 took 2 rounds (one
  beta-redex matching failure, one association mismatch). S4 took 10 rounds, of
  which the *last six* were one defect: `((n - 1 - i) : ℤ)` — a `: ℤ` ascription
  makes the subtraction *untruncated* ℤ subtraction, so it differs from the
  ℕ-truncated cast a `Nat.choose` bridge produces, and `ring`/`ring_nf` reported
  it as an opaque three-term sum. The fix came only from *deleting* the failing
  tactic and recompiling to read the pristine goal. Lessons 13–16 in
  `MATHLIB_API_LESSONS.md` record this, the `_shift`-lemma pattern, the
  definition-before-use trap, and the "read the pristine goal" habit.
- **The DONE gate caught two record bugs, not the mathematics**: a chunk file
  without a `status.tsv` row, and a comma-separated `renders` field where the
  schema wants space-separated. Both are exactly the kind of thing that only a
  machine check finds.
- **Next, in order:** (1) re-align `M1-FRAG-05/06`'s boundaries to the real region
  lines (the factorial display continues past `P007-R1` l12 into R2/R3) and write
  them; (2) the `M1-ASM-A…E` assemblies, where an undischarged leaf hypothesis
  would be the signature of a circularity; (3) `Q-003` must be resolved before
  any leaf from pp. 31–32.
- **The pp. 7–8 structure, measured 2026-09-28 (this replaces the estimated
  boundaries in the plan table).** The display is a *chain*: `=` (the absorbed
  tail + four explicit terms, S3), `⇔ [filtered sum] + [fifteen sums in factorial
  form]` (S4 + the ten conversions of `M1-FRAG-05`), then repeated
  `⇒ [X⁴ sums rearranged]` / `≡ … (mod n^{4s+2})` pairs — the congruence lines
  carry the author's own `vì 5s ≥ 4s+2` justification and are where every dropped
  term needs a divisibility side condition (the F3/F4 risk of this part of the
  proof). Region line counts: `P007-R1` 7 non-empty lines, `P007-R2` 8,
  `P007-R3` 6 (l0–l4 continue R2 l6 — one display across the page break),
  `P008-R1` 7, `P008-R2` 7, `P008-R3` 7. **A duplicate print is not a second
  step**: `P008-R1` l2–l6 and `P008-R3` l0–l4 restate the same X⁴ sums around the
  intervening lines, so the step count follows the `≡`/`⇒` transitions, not the
  printed lines.
- **Round ledger at the leaf's close: 55 rows — 19 S1 / 29 F2 / 2 ENV / 2 F1 /
  2 PROBE.** The two F1s are our own transcription/encoding defects, not the
  author's: the p. 6 R3 `ℕ`-unsafe exponent form (round 31) and the `: ℤ`
  ascription of S4 (round 52). Cost model (measured): a *failing* round costs
  7–24 s because the Mathlib oleans are cached, so iterate freely on compile
  errors; only successful rounds with heavy `ring`/`omega` take minutes.
