"""Stage 1 gate: verify extraction fidelity between the two engines.

Usage:
    python fidelity_check.py <extract_dir>

Reads extract_pypdf.txt, extract_pymupdf.txt, extract_meta.json.
Writes fidelity_report.json with per-page verdicts and an overall verdict.

Human review surface: every non-OK page additionally gets
<extract_dir>/review/page-NNN.html — the rendered page (or the exact
render command when no render exists) beside BOTH engine extracts with
non-equal token spans highlighted, plus the divergence windows and
unique-token samples. Open <extract_dir>/review/index.html in a browser
for the review queue. fidelity_report.json stays the machine contract
(progress.py --check reads it); the HTML is a view generated from it.

What "fidelity" means here: the two text-extraction engines (pypdf,
pymupdf) must agree on the author's character stream closely enough that
the transcripts are safe to transcribe from. The rendered PDF stays
authoritative; this gate only decides HOW a page may be transcribed:
from the text layer (OK) or from the render (MANUAL).

Gate semantics (exit codes):
    0 — PASS or PASS_WITH_MANUAL: page counts equal 33 and both engines
        produced text on every page. PASS_WITH_MANUAL means some page has
        verdict MANUAL: its transcription must come from the rendered page
        and be recorded in the consuming chunk's `renders` field.
    1 — FAIL: some page has verdict FAIL (no text in an engine) or REVIEW
        (a prose page diverges beyond threshold), or the transcript page
        markers do not split into 33 pages. Stop the pipeline; inspect
        fidelity_report.json and route the page to MANUAL transcription
        from the render (see 02-chunks/schema.md).

Metrics (all computed on NFC-normalized text):
    token_overlap  legacy set-Jaccard on whitespace tokens (+8-char
                   shingles); kept for continuity with earlier reports,
                   NOT a verdict driver.
    seq_overlap    difflib.SequenceMatcher ratio on the token STREAM
                   (order- and multiplicity-aware, autojunk off). Primary
                   verdict driver. Line-based comparison is deliberately
                   NOT used: the engines break lines differently (pymupdf
                   emits ~5x more line breaks), so line diffs are noise.
    digit_overlap  SequenceMatcher ratio on the page's concatenated digit
                   characters. 1.0 means the digit streams are byte
                   identical. Anything below 1.0 escalates the verdict one
                   step: digits are load-bearing for Lean transcription.
    math_density   fraction of characters that are digits, math symbols, or
                   symbol-like unicode. Pages above threshold (or in
                   KNOWN_MATH_PAGES) are math-dense: divergence there is
                   EXPECTED and routes to MANUAL, not FAIL.

Per-page verdicts (fidelity_report.json `verdict`):
    OK      engines agree; the text layer is safe as navigation.
    MANUAL  math-dense page diverges as expected — transcribe from
            the render and record the read per chunk.
    REVIEW  prose page diverges more than expected — inspect.
    FAIL    one engine produced no text for the page.

Non-OK pages carry actionables, not just a number: a preferred_engine
heuristic (more readable words, fewer degenerate glyph-runs — navigation
aid only, MANUAL pages transcribe from the render regardless), first
divergent token windows with context, opcode token counts, and top
unique-token samples per engine.

Top-level transcript_sha256 pins the exact transcript bytes the verdicts
were computed on (extract_meta.json only carries counts, so a changed
transcript with equal length would otherwise bind identically).

Chunk consumption: `pipeline/progress.py --check` validates every DONE
chunk's evidence block (source_pdf_sha / extract_run_sha / fidelity /
renders / lean_decls) against this report.

Deliberately conservative: math divergence means "needs human eyes",
not "pipeline is broken".
"""
import difflib
import hashlib
import html
import json
import re
import sys
import unicodedata
from collections import Counter
from pathlib import Path

import regions

EXPECTED_PAGES = 33
# Verdict driver is seq_overlap; numbers kept from the legacy gate.
SEQ_OK_MATH = 0.80
SEQ_OK_PROSE = 0.50
# Measured density: p1 (title) ~0.07 is the only prose-like page; pp. 2-6
# sit at 0.16-0.23, everything else >= 0.25. 0.15 separates cleanly.
DENSITY_THRESHOLD = 0.15
# Front pages carry lemma statements/proofs regardless of density.
KNOWN_MATH_PAGES = {1, 2, 3, 4, 5}

DIFF_CONTEXT = 5
DIFF_CAP = 400
UNIQUE_SAMPLES = 8
REVIEW_DIRNAME = "review"

MATH_SYMS = set("=+-−^*/<>≤≥≠≈±×÷∫∑∏∂√∞∈∉∀∃∧∨¬⇒⇔→←()[]{}_|")

PAGE_SPLIT = re.compile(r"=== PAGE \d+ ===")

METHOD = (
    "fidelity_check v2: NFC + legacy token-Jaccard (continuity) + "
    "token-stream seq (verdict driver) + digit-stream seq (tripwire) + "
    "density-routed math/prose verdicts + token-window diffs"
)


def nfc(text: str) -> str:
    return unicodedata.normalize("NFC", text)


def legacy_tokenize(text: str) -> set[str]:
    """Original set-Jaccard tokenization (+8-char shingles), NFC-normalized.

    Kept so `token_overlap` stays comparable across reports. Order- and
    multiplicity-blind by construction; see `seq_overlap` for the verdict.
    """
    toks = set()
    for w in text.split():
        toks.add(re.sub(r"\s+", "", w))
    compact = re.sub(r"\s+", "", text)
    for i in range(0, len(compact), 8):
        toks.add(compact[i : i + 8])
    return toks


def page_tokens(text: str) -> list[str]:
    return [w for w in nfc(text).split() if w]


def seq_ratio(la: list[str], lb: list[str]) -> float:
    if not la and not lb:
        return 1.0
    return difflib.SequenceMatcher(None, la, lb, autojunk=False).ratio()


def digit_ratio(a: str, b: str) -> float:
    sa = "".join(re.findall(r"\d", a))
    sb = "".join(re.findall(r"\d", b))
    if not sa and not sb:
        return 1.0
    return difflib.SequenceMatcher(None, sa, sb, autojunk=False).ratio()


def math_density(text: str) -> float:
    t = nfc(text)
    if not t.strip():
        return 0.0
    sym = sum(
        1
        for c in t
        if c in MATH_SYMS or c.isdigit() or unicodedata.category(c) in ("No", "Sm", "Sk")
    )
    return sym / max(len(t), 1)


def line_count(text: str) -> int:
    return sum(1 for line in nfc(text).splitlines() if line.strip())


def pua_count(text: str) -> int:
    """Private-use + replacement chars: engine-emitted garbage signal."""
    return sum(1 for c in nfc(text) if unicodedata.category(c) == "Co" or c == "\ufffd")


_VOWELS = set("aeiouyAEIOUY")


def _base_vowel_char(c: str) -> str:
    """First char of the NFD decomposition: strips Vietnamese diacritics."""
    decomposed = unicodedata.normalize("NFD", c)
    return decomposed[0] if decomposed else c


def readability(text: str) -> dict[str, int]:
    """Readability signals for the preferred-engine heuristic (navigation aid).

    words: tokens of length >= 3 that are all letters and contain a vowel
        (diacritic-aware via NFD base chars). Rewards real prose/math terms.
    degenerate: glyph-runs that are never author text -- repeated single
        chars ("nn", "--") or pure punctuation ("()", "--+"). Penalized.
    Measured live: on math pages pymupdf has ~3-20x fewer degenerate runs
    and comparable word counts, so the margin is decisive where it matters.
    """
    words = degenerate = 0
    for tok in nfc(text).split():
        if not tok:
            continue
        alpha = all(c.isalpha() or c == "_" for c in tok)
        if len(tok) >= 3 and alpha and any(
            _base_vowel_char(c) in _VOWELS for c in tok if c.isalpha()
        ):
            words += 1
        if len(tok) >= 2 and (
            len(set(tok)) == 1 or not any(c.isalnum() for c in tok)
        ):
            degenerate += 1
    return {"words": words, "degenerate": degenerate}


def split_pages(transcript: str) -> list[str]:
    parts = PAGE_SPLIT.split(transcript)
    return [p for p in parts if p.strip()]


def divergence_windows(la: list[str], lb: list[str]) -> dict:
    """First non-equal opcode with context + equal-token counts."""
    sm = difflib.SequenceMatcher(None, la, lb, autojunk=False)
    equal = 0
    first = None
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            equal += i2 - i1
        elif first is None:
            first = (tag, i1, i2, j1, j2)
    out = {
        "equal_tokens": equal,
        "total_pypdf_tokens": len(la),
        "total_pymupdf_tokens": len(lb),
        "first_op": first[0] if first else "equal",
        "first_pypdf": "",
        "first_pymupdf": "",
    }
    if first:
        _, i1, i2, j1, j2 = first
        a0, a1 = max(i1 - DIFF_CONTEXT, 0), min(i2 + DIFF_CONTEXT, len(la))
        b0, b1 = max(j1 - DIFF_CONTEXT, 0), min(j2 + DIFF_CONTEXT, len(lb))
        out["first_pypdf"] = " ".join(la[a0:a1])[:DIFF_CAP]
        out["first_pymupdf"] = " ".join(lb[b0:b1])[:DIFF_CAP]
    return out


def unique_samples(la: list[str], lb: list[str], n: int = UNIQUE_SAMPLES) -> list[list]:
    other = set(lb)
    ranked = sorted(
        ((t, c) for t, c in Counter(la).items() if t not in other),
        key=lambda kv: (-kv[1], kv[0]),
    )
    return [[t, c] for t, c in ranked[:n]]


def page_image_href(directory: Path, page_no: int) -> str | None:
    """Href from review/ to this page's renderer output, full page preferred."""
    full = sorted(directory.glob(f"page-{page_no:03d}-*-full.png"))
    any_render = sorted(directory.glob(f"page-{page_no:03d}-*.png"))
    chosen = full or any_render
    return f"../{chosen[0].name}" if chosen else None


def mark_columns(la: list[str], lb: list[str]) -> tuple[str, str]:
    """HTML for both token columns with non-equal spans wrapped in <mark>.

    pypdf side marks class 'd' (divergent there), pymupdf side class 'i'.
    Tokens are HTML-escaped and joined with single spaces.
    """
    opcodes = difflib.SequenceMatcher(None, la, lb, autojunk=False).get_opcodes()
    left: list[str] = []
    right: list[str] = []
    for tag, i1, i2, j1, j2 in opcodes:
        a = " ".join(la[i1:i2])
        b = " ".join(lb[j1:j2])
        if tag == "equal":
            left.append(html.escape(a))
            right.append(html.escape(b))
        else:
            if a:
                left.append(f'<mark class="d">{html.escape(a)}</mark>')
            if b:
                right.append(f'<mark class="i">{html.escape(b)}</mark>')
    return " ".join(left), " ".join(right)


REVIEW_STYLE = """
body{font:14px/1.45 system-ui,sans-serif;margin:0;padding:14px;background:#f6f7f9;color:#141414}
header{margin-bottom:10px}
h1{font-size:17px;margin:0 0 6px}
.chips span{display:inline-block;background:#fff;border:1px solid #d9dde3;border-radius:99px;padding:2px 9px;margin:2px 4px 0 0;font-size:12px}
main{display:grid;grid-template-columns:minmax(300px,42%) 1fr;gap:14px;align-items:start}
.render{position:sticky;top:10px;background:#fff;border:1px solid #d9dde3;border-radius:8px;padding:8px}
.render img{max-width:100%;height:auto;display:block}
.callout{background:#fff6d6;border:1px solid #ffe08a;border-radius:8px;padding:12px;font-size:13px}
code{display:inline-block;margin-top:6px;background:#fff;border:1px solid #e6d9a0;padding:4px 6px;border-radius:4px;font-size:12px;word-break:break-all}
pre{white-space:pre-wrap;word-break:break-word;background:#fff;border:1px solid #d9dde3;border-radius:8px;padding:10px;font:12px/1.55 ui-monospace,Consolas,monospace;max-height:55vh;overflow:auto}
pre+pre{margin-top:10px}
h3{font-size:13px;margin:14px 0 4px;color:#444}
mark.d{background:#ffd7d7;color:#7d0e0e}
mark.i{background:#ffedb0;color:#6d5200}
details{margin-top:10px;background:#fff;border:1px solid #d9dde3;border-radius:8px;padding:8px 10px}
summary{cursor:pointer;font-weight:600;font-size:13px}
.cols{display:grid;grid-template-columns:1fr 1fr;gap:10px}
a{color:#0b57d0}
.note{font-size:12px;color:#555;margin-top:8px}
table{border-collapse:collapse;background:#fff;font-size:13px}
th,td{border:1px solid #d9dde3;padding:5px 10px;text-align:left}
th{background:#eef1f5}
.region{background:#fff;border:1px solid #d9dde3;border-radius:8px;padding:8px 10px;margin-top:8px}
.region.bad{border-left:4px solid #d3302f}
.region.warn{border-left:4px solid #e0a800}
.region-head{display:flex;gap:8px;align-items:center;flex-wrap:wrap;font-size:12px}
.rid{display:inline-block;background:#eef1f5;border:1px solid #d9dde3;border-radius:99px;padding:1px 8px;font-weight:600}
.flag{display:inline-block;border-radius:99px;padding:1px 8px;font-size:11px;border:1px solid}
.flag.f-bad{background:#ffe2e2;border-color:#f0a6a6;color:#8a1212}
.flag.f-warn{background:#fff3cd;border-color:#ffd870;color:#6d5200}
.flag.f-note{background:#e8f0fe;border-color:#b9cdf5;color:#1a4599}
.copy{font:12px system-ui;border:1px solid #d9dde3;background:#fff;border-radius:6px;padding:2px 10px;cursor:pointer}
.copy:hover{background:#eef1f5}
.region pre{margin-top:8px}
.export-note{font-size:12px;color:#555;margin-top:6px}
"""


COPY_SCRIPT = """
<script>
document.querySelectorAll('button.copy').forEach(function (button) {
  button.addEventListener('click', function () {
    var pre = button.closest('.region').querySelector('.latex-src');
    var text = pre.textContent;
    function done() {
      button.textContent = 'copied';
      setTimeout(function () { button.textContent = 'copy'; }, 1200);
    }
    function fallback() {
      var range = document.createRange();
      range.selectNodeContents(pre);
      var selection = window.getSelection();
      selection.removeAllRanges();
      selection.addRange(range);
      try {
        document.execCommand('copy');
        done();
      } catch (e) {
        button.textContent = 'select manually';
      }
    }
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(done, fallback);
    } else {
      fallback();
    }
  });
});
</script>
"""


def _flag_class(label: str) -> str:
    if label in ("digit mismatch", "stale signoff"):
        return "f-bad"
    if label.startswith("PUA"):
        return "f-warn"
    return "f-note"


def build_region_section(
    page_no: int, region_record: dict | None, source_pdf: str
) -> str:
    """Vision→LaTeX transcription rows with review flags + copy buttons."""
    if region_record is None:
        return (
            '<div class="callout">no region record — run <code>regions.py plan '
            f"{html.escape(source_pdf)} {page_no} --spec …</code></div>"
        )
    rows = regions.review_rows(region_record)
    status = str(region_record.get("status", "DRAFT"))
    blocks = []
    for row in rows:
        flags = row["flags"]
        classes = "region"
        if any(f in ("digit mismatch", "stale signoff") for f in flags):
            classes += " bad"
        elif any(f.startswith("PUA") for f in flags):
            classes += " warn"
        flag_html = "".join(
            f'<span class="flag {_flag_class(f)}">{html.escape(f)}</span>'
            for f in flags
        )
        crop = str(row.get("crop", ""))
        crop_html = (
            f'<a class="crop" href="../{html.escape(crop)}">crop</a>' if crop else ""
        )
        blocks.append(
            f'<div class="{classes}"><div class="region-head">'
            f'<span class="rid">{html.escape(row["id"])}</span>{crop_html}{flag_html}'
            f'<button class="copy" type="button">copy</button></div>'
            f'<pre class="latex-src">{html.escape(row["latex"])}</pre></div>'
        )
    return (
        f'<div class="chips"><span><b>record</b> {html.escape(status)}</span></div>'
        + "".join(blocks)
        + '<p class="export-note">External editor: <code>regions.py export '
          f"pipeline/01-extract/regions/p{page_no:03d}.yml --out review.tex"
          "</code> renders these blocks as one amsmath/xcolor document.</p>"
        + COPY_SCRIPT
    )


def build_review_html(
    entry: dict,
    text_a: str,
    text_b: str,
    image_href: str | None,
    source_pdf: str,
    region_record: dict | None = None,
) -> str:
    """One page's review surface: render beside both marked extracts."""
    page_no = int(entry.get("page", 0))
    verdict = str(entry.get("verdict", "?"))
    marked_a, marked_b = mark_columns(page_tokens(text_a), page_tokens(text_b))
    if image_href:
        visual = (
            f'<div class="render"><img src="{html.escape(image_href)}" '
            f'alt="render of page {page_no}"></div>'
        )
    else:
        visual = (
            '<div class="callout"><b>No render on file for this page.</b><br>'
            "Produce the authoritative image (required for MANUAL review):<br>"
            f"<code>python pipeline/01-extract/render_pdf.py "
            f"{html.escape(source_pdf)} &lt;outdir&gt; --page {page_no} --dpi 300</code>"
            "</div>"
        )
    chip_data = [
        ("verdict", verdict),
        ("seq", entry.get("seq_overlap", "—")),
        ("digits", entry.get("digit_overlap", "—")),
        ("density", entry.get("math_density", "—")),
        ("tokens", entry.get("token_overlap", "—")),
        ("preferred", entry.get("preferred_engine", "—")),
    ]
    chips = "".join(
        f'<span><b>{html.escape(str(k))}</b> {html.escape(str(v))}</span>'
        for k, v in chip_data
    )
    diff = entry.get("diff") or {}
    uniq_a = ", ".join(f"{html.escape(str(t))}×{c}" for t, c in (entry.get("unique_pypdf") or [])) or "—"
    uniq_b = ", ".join(f"{html.escape(str(t))}×{c}" for t, c in (entry.get("unique_pymupdf") or [])) or "—"
    footer = (
        '<details><summary>first divergent span (engine token windows)</summary>'
        "<div class=\"cols\">"
        f"<div><h3>pypdf</h3><pre>{html.escape(str(diff.get('first_pypdf', '')))}</pre></div>"
        f"<div><h3>pymupdf</h3><pre>{html.escape(str(diff.get('first_pymupdf', '')))}</pre></div>"
        "</div></details>"
        '<details><summary>unique tokens (how each engine diverges)</summary>'
        "<div class=\"cols\">"
        f"<div><h3>only in pypdf</h3><pre>{uniq_a}</pre></div>"
        f"<div><h3>only in pymupdf</h3><pre>{uniq_b}</pre></div>"
        "</div></details>"
    )
    region_section = build_region_section(page_no, region_record, source_pdf)
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Page {page_no} — {html.escape(verdict)} review</title>
<style>{REVIEW_STYLE}</style>
</head>
<body>
<header>
<h1>Page {page_no} — fidelity {html.escape(verdict)}</h1>
<div class="chips">{chips}</div>
<p class="note">Render (left) is authoritative; extracts are navigation.
<mark class="d">pink</mark> = divergent on the pypdf side,
<mark class="i">amber</mark> = on the pymupdf side. Colors in the PDF
(green/red/bold) are NOT extracted by either engine.</p>
</header>
<main>
{visual}
<section>
<h3>extract — pypdf</h3>
<pre>{marked_a}</pre>
<h3>extract — pymupdf</h3>
<pre>{marked_b}</pre>
{footer}
<h3>LaTeX transcription (regions)</h3>
{region_section}
</section>
</main>
</body>
</html>
"""


def region_state(record: dict | None) -> str:
    """Index cell: '—' | 'DRAFT' | 'REVIEWED' | 'REVIEWED ⚠n' (n = bad regions)."""
    if record is None:
        return "—"
    if record.get("status") != "REVIEWED":
        return str(record.get("status") or "DRAFT")
    bad = sum(
        1
        for row in regions.review_rows(record)
        if any(f in ("digit mismatch", "stale signoff") for f in row["flags"])
    )
    return "REVIEWED" if bad == 0 else f"REVIEWED ⚠{bad}"


def build_index_html(entries: list[tuple[dict, str | None, str]], source_pdf: str) -> str:
    """Review queue: one row per non-OK page, render-missing commands listed."""
    rows = []
    missing_cmds = []
    for entry, href, regions_cell in entries:
        n = int(entry.get("page", 0))
        note = "" if href else " · render missing"
        if not href:
            missing_cmds.append(
                f"<code>python pipeline/01-extract/render_pdf.py {html.escape(source_pdf)}"
                f" &lt;outdir&gt; --page {n} --dpi 300</code>"
            )
        cell = lambda k, d="—": html.escape(str(entry.get(k, d)))
        rows.append(
            f"<tr><td>{n}</td><td>{cell('verdict')}</td><td>{cell('seq_overlap')}</td>"
            f"<td>{cell('digit_overlap')}</td><td>{cell('math_density')}</td>"
            f"<td>{cell('preferred_engine')}</td>"
            f"<td>{html.escape(regions_cell)}</td>"
            f'<td><a href="page-{n:03d}.html">open</a>{note}</td></tr>'
        )
    render_block = (
        ("<p><b>Renders still needed</b>:</p>" + "<br>".join(missing_cmds))
        if missing_cmds
        else "<p>All listed pages have a render on file.</p>"
    )
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Fidelity review queue</title>
<style>{REVIEW_STYLE}</style>
</head>
<body>
<header>
<h1>Fidelity review queue — pages needing human eyes</h1>
<p class="note">Render is authoritative; both extracts are navigation aids.
Machine contract: <code>../fidelity_report.json</code>.</p>
</header>
<table>
<tr><th>page</th><th>verdict</th><th>seq</th><th>digits</th><th>density</th><th>preferred</th><th>regions</th><th>review</th></tr>
{"".join(rows)}
</table>
{render_block}
</body>
</html>
"""


def write_review(
    d: Path,
    pages: list[dict],
    p1: list[str],
    p2: list[str],
    source_pdf: str,
) -> list[str]:
    """Write review/ HTML for every non-OK page; returns the file names."""
    targets = [e for e in pages if e.get("verdict") != "OK"]
    if not targets:
        return []
    review = d / REVIEW_DIRNAME
    review.mkdir(exist_ok=True)
    for stale in review.glob("page-*.html"):
        stale.unlink()
    entries: list[tuple[dict, str | None, str]] = []
    written = []
    for entry in targets:
        i = int(entry.get("page", 0)) - 1
        a = p1[i] if 0 <= i < len(p1) else ""
        b = p2[i] if 0 <= i < len(p2) else ""
        page_no = int(entry["page"])
        href = page_image_href(d, page_no)
        try:
            record = regions.load_page_record(
                regions.REGIONS_DIR / f"p{page_no:03d}.yml"
            )
        except OSError:
            record = None
        name = f"page-{page_no:03d}.html"
        (review / name).write_text(
            build_review_html(entry, a, b, href, source_pdf, record),
            encoding="utf-8",
            newline="\n",
        )
        written.append(name)
        entries.append((entry, href, region_state(record)))
    (review / "index.html").write_text(
        build_index_html(entries, source_pdf), encoding="utf-8", newline="\n"
    )
    return written


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    d = Path(sys.argv[1])
    meta = json.loads((d / "extract_meta.json").read_text(encoding="utf-8"))
    raw1 = (d / "extract_pypdf.txt").read_bytes()
    raw2 = (d / "extract_pymupdf.txt").read_bytes()
    p1, p2 = split_pages(raw1.decode("utf-8")), split_pages(raw2.decode("utf-8"))

    page_count_ok = len(p1) == EXPECTED_PAGES and len(p2) == EXPECTED_PAGES
    pages = []
    overall = "PASS"
    if (
        meta["pypdf_pages"] != EXPECTED_PAGES
        or meta["pymupdf_pages"] != EXPECTED_PAGES
        or not page_count_ok
    ):
        overall = "FAIL"

    for i in range(max(len(p1), len(p2))):
        a = p1[i] if i < len(p1) else ""
        b = p2[i] if i < len(p2) else ""
        page_no = i + 1
        na, nb = nfc(a), nfc(b)

        wa, wb = legacy_tokenize(na), legacy_tokenize(nb)
        overlap = len(wa & wb) / max(len(wa | wb), 1)
        la, lb = page_tokens(na), page_tokens(nb)
        seq = seq_ratio(la, lb)
        dig = digit_ratio(na, nb)
        dens = max(math_density(na), math_density(nb))
        dense = dens >= DENSITY_THRESHOLD or page_no in KNOWN_MATH_PAGES

        has_text = bool(na.strip()) and bool(nb.strip())
        if not has_text:
            verdict = "FAIL"
        elif dense:
            verdict = "MANUAL" if seq < SEQ_OK_MATH else "OK"
        else:
            verdict = "OK" if seq > SEQ_OK_PROSE else "REVIEW"
        if dig < 1.0 and verdict == "OK":
            verdict = "MANUAL" if dense else "REVIEW"
        if verdict in ("FAIL", "REVIEW"):
            overall = "FAIL"

        ra, rb = readability(na), readability(nb)
        pa, pb = pua_count(na), pua_count(nb)
        # Fewer degenerate runs first, then more readable words. Tie only
        # on exact equality; measured live this never ties (pymupdf wins
        # 33/33 on this PDF).
        key_a = (ra["degenerate"], -ra["words"])
        key_b = (rb["degenerate"], -rb["words"])
        preferred = "pypdf" if key_a < key_b else ("pymupdf" if key_b < key_a else "tie")

        entry = {
            "page": page_no,
            "pypdf_chars": len(a),
            "pymupdf_chars": len(b),
            "pypdf_lines": line_count(na),
            "pymupdf_lines": line_count(nb),
            "token_overlap": round(overlap, 3),
            "seq_overlap": round(seq, 3),
            "digit_overlap": round(dig, 3),
            "math_density": round(dens, 3),
            "math_dense": dense,
            "verdict": verdict,
            "preferred_engine": preferred,
            "words_pypdf": ra["words"],
            "degen_pypdf": ra["degenerate"],
            "words_pymupdf": rb["words"],
            "degen_pymupdf": rb["degenerate"],
            "pua_pypdf": pa,
            "pua_pymupdf": pb,
        }
        if verdict != "OK":
            entry["diff"] = divergence_windows(la, lb)
            entry["unique_pypdf"] = unique_samples(la, lb)
            entry["unique_pymupdf"] = unique_samples(lb, la)
        pages.append(entry)

    if overall != "FAIL":
        overall = (
            "PASS_WITH_MANUAL"
            if any(p["verdict"] == "MANUAL" for p in pages)
            else "PASS"
        )

    report = {
        "source_sha256": meta["sha256"],
        "transcript_sha256": {
            "pypdf": hashlib.sha256(raw1).hexdigest(),
            "pymupdf": hashlib.sha256(raw2).hexdigest(),
        },
        "expected_pages": EXPECTED_PAGES,
        "page_count_ok": page_count_ok,
        "method": METHOD,
        "overall": overall,
        "pages": pages,
    }
    (d / "fidelity_report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n"
    )
    n_manual = sum(1 for p in pages if p["verdict"] == "MANUAL")
    n_fail = sum(1 for p in pages if p["verdict"] in ("FAIL", "REVIEW"))
    print(f"overall={overall} manual_pages={n_manual} failing_pages={n_fail}")
    review_files = write_review(d, pages, p1, p2, str(meta.get("source_pdf", "")))
    if review_files:
        print(f"review={d / REVIEW_DIRNAME / 'index.html'} ({len(review_files)} pages)")
    return 0 if overall in ("PASS", "PASS_WITH_MANUAL") else 1


if __name__ == "__main__":
    raise SystemExit(main())
