# Author feedback (`05-feedback/`)

When Lean verification fails on a chunk, the failure belongs to one of two
worlds: OUR transcription/formalization is wrong, or THE PROOF STEP is
wrong or has a gap. This track produces, for the second world, an artifact
the original author can answer quickly — without reading Lean.

## Triage rule (decide within one session, never let a failure sit)

1. Re-run the chunk's sympy test. Counterexample found → suspect OUR
   transcription first: re-check `source_text` against the PDF.
2. If transcription is faithful and sympy still refutes it → the CLAIM is
   false as stated. Open a query (template below).
3. If Lean rejects a step sympy cannot refute → the step may have a GAP
   (uses an unproven sub-claim). Open a query asking for the missing
   justification, quoting the exact inference.
4. If OUR formalization is wrong (chunk faithful, claim true, Lean stub
   mismodelled) → fix the Lean file, no query needed.

Never open a query until steps 1–4 rule out our own error. Every query
must reproduce WITHOUT Lean: sympy script + numbers, or a quoted
inference with page/line reference.

## Query file format (`queries/Q-NNN-short-title.md`)

- Heading: `# Q-NNN title [OPEN|ANSWERED|RESOLVED]`.
- Sections: Chunk + PDF ref / What we formalized (Lean statement in
  plain math) / What failed (Lean error or sympy counterexample, with
  reproduction command) / Minimal example (smallest numbers/formulas
  showing the issue) / Question for the author (one precise question) /
  Attachments (sympy script path, Lean file path, PDF screenshot).
- Status lifecycle: OPEN → ANSWERED (author replied, fix pending) →
  RESOLVED (chunk updated, Lean compiles, sympy passes; link the commit).

## Response kit

Each RESOLVED query keeps its reproduction artifacts so the author (or a
referee) can re-run them: the sympy script stays in `04-sympy/`, the Lean
file stays in `03-lean/`, and the query records both paths plus the
resolving commit hash.

## Author report (`render_report.py`)

Send the author a package they can answer **without Lean and without the
repository**:

    python pipeline/05-feedback/render_report.py            # build + verify
    python pipeline/05-feedback/render_report.py --zip      # + report.zip
    python pipeline/05-feedback/render_report.py --no-verify

Reads `queries/Q-NNN-*.md` plus the chunk records (`02-chunks/chunks/*.yml`)
and writes a self-contained `report/`:

- `report/index.html` — overview: open queries, chunk status, how to respond
  (bilingual vi/en chrome, query text kept verbatim);
- `report/Q-NNN.html` — one page per issue, in reading order: the question
  first (highlighted card), what the print says, **the printed pages with the
  cited regions boxed in red** (rects from `01-extract/regions/pNNN.yml`
  overlaid on the full-page renders — the query's own `P0NNN-RM` mentions pick
  the regions, otherwise every region of the chunk), the same lines **typeset
  by KaTeX**, what Lean formalized plus the verified declaration list, the
  F3/F4 classification notes, and a reply box (screen textarea, ruled lines
  when printed);
- `report/reply-Q-NNN.md` — plain-text reply template for answering by email;
- `report/assets/…` — every referenced file (renders, region crops, the cited
  review pages, linked sources, KaTeX), mirroring its `pipeline/`-relative
  path. Files are **hardlinked** when the filesystem allows (fallback:
  copy) so the package adds no bytes to the checkout.

**Gate 1 — ship it.** After writing, the script zips the report, extracts it
to a temp directory and checks that every `src`/`href` and every CSS `url()`
resolves *inside* the extracted tree, **and** that every packed stylesheet
keeps its `@font-face` blocks (each still carrying a `url()`) plus KaTeX's
`.katex` rule — the font binding; a stylesheet that loses them renders formulas
in system fonts and looks wrong (`verify: N files, N refs checked …`).
Exit 1 on any miss; `--no-verify` skips it. `--zip` also writes
`<out>.zip` for attaching to an email.

**Gate 2 — many reports, no interference.** Each `--out` directory owns its
`assets/` and prunes only its own generated files (`index.html`, `Q-*.html`,
`reply-*.md`, `assets/`) before rebuilding; it refuses to touch a directory it
did not generate. Two report directories can be built in any order without
sharing state.

**Not packed:** `01-extract/out/review/index.html` (it links all 19 manual
review pages, which would drag in the whole review surface). The report packs
the individual `review/page-NNN.html` pages the query cites — each carries its
own render and crops, so it works standalone.

**KaTeX** is vendored at `05-feedback/vendor/katex/` (MIT, `LICENSE` kept,
woff2 fonts only). The report page binds those fonts through its
`<link rel="stylesheet" href="assets/…/katex.min.css">`; the packed copy of
that CSS keeps all20 `@font-face` declarations pointing at the shipped
`fonts/*.woff2` and drops only the woff/ttf entries whose files are not
shipped — trimming is restricted to the inside of `src:` lists (a greedy
pattern there used to swallow `}@font-face{…` and silently unbind the fonts;
the verify gate now rejects that). Rendering is client-side, no server; if
JavaScript or KaTeX is unavailable the raw text stays visible, formulas never
hide content.

`report/` is generated **and gitignored** (same policy as `01-extract/out/`:
the checkout carries the script and the sources, not the bulky regenerable
output). Build it on demand, ship it with `--zip`, and never hand-edit it.
Also update `check()`/this README when adding a new kind of reference.
