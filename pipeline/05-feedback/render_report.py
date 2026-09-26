#!/usr/bin/env python3
"""Author report generator for the Lean verification findings (05-feedback/).

Renders every author query, together with the chunk record around it, as a
small static HTML report the original author can read **without Lean**:

  report/index.html          overview: open questions, chunk status, instructions
  report/Q-NNN.html          one page per query: the question, what the print
                             says (render images), what Lean verified, reply box
  report/reply-Q-NNN.md      plain-text reply template for answering by email

It also cross-checks the ledger while building the report: every BLOCKED chunk
must have a query, every query must point at an existing chunk, and every
referenced image/render must exist on disk. Warnings are printed and shown in
the index; the report is still written (an incomplete report beats none).

Usage:
    python pipeline/05-feedback/render_report.py
    python pipeline/05-feedback/render_report.py --out report --quiet

Exit codes: 0 report written (warnings allowed), 1 no queries or an
unparseable query file, 2 report directory not writable.
"""

from __future__ import annotations

import argparse
import datetime
import html
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent          # pipeline/05-feedback
PIPE = HERE.parent                              # pipeline
ROOT = PIPE.parent                              # repo root
QUERIES_DIR = HERE / "queries"
CHUNKS_DIR = PIPE / "02-chunks" / "chunks"
RENDER_DIR = PIPE / "01-extract" / "out"
REVIEW_DIR = RENDER_DIR / "review"
DEFAULT_OUT = HERE / "report"

TITLE_RE = re.compile(r"^#\s+(.*)$")
HEADING_RE = re.compile(r"^##\s+(.*?)\s*$")
STATUS_RE = re.compile(r"\[(OPEN|ANSWERED|RESOLVED)\]\s*$")
CHUNK_REF_RE = re.compile(r"\b(L\d+-[A-Z0-9][A-Z0-9-]*)\b")
IMAGE_REF_RE = re.compile(r"[\w.+-]+(?:/[\w.+-]+)*\.(?:png|jpg|jpeg)")
PATH_REF_RE = re.compile(
    r"[\w.+-]+(?:/[\w.+-]+)*\.(?:md|py|lean|yml|yaml|png|html|log|txt|tsv)")
CLASS_MARK_RE = re.compile(r"^F([1-4])(?=[\s(:])")   # not "F1)." inside prose
QUERY_MARK_RE = re.compile(r"\b(Q-\d+)\b")

STYLE = """
:root{--ink:#141414;--mut:#5b6470;--line:#d9dde3;--bg:#f6f7f9;--card:#fff;
      --blue:#0b57d0;--amber:#fff6d6;--red:#ffe2e2;--green:#e6f4ea}
*{box-sizing:border-box}
body{font:15px/1.55 system-ui,-apple-system,"Segoe UI",sans-serif;margin:0;
     padding:18px 16px 40px;background:var(--bg);color:var(--ink);max-width:1100px}
a{color:var(--blue)}
h1{font-size:23px;margin:.2em 0 .35em}
h2{font-size:17px;margin:1.3em 0 .45em;border-bottom:2px solid var(--line);padding-bottom:.2em}
h3{font-size:15px;margin:1.1em 0 .35em;color:#2b3440}
h4,h5,h6{font-size:14px;margin:1em 0 .3em;color:#2b3440}
p,li{margin:.45em 0}
code,pre{font-family:ui-monospace,Consolas,"Courier New",monospace;font-size:13px}
code{background:#fff;border:1px solid var(--line);border-radius:4px;padding:1px 5px}
pre{white-space:pre-wrap;word-break:break-word;background:#fff;border:1px solid var(--line);
    border-radius:8px;padding:10px 12px}
blockquote{margin:.6em 0;padding:8px 12px;background:#fff;border-left:4px solid var(--blue);
           border-radius:0 8px 8px 0}
.chips span{display:inline-block;background:#fff;border:1px solid var(--line);
            border-radius:99px;padding:2px 10px;margin:3px 6px 0 0;font-size:13px}
.st-OPEN{background:var(--red);border-color:#f0a6a6;color:#8a1212;font-weight:600}
.st-ANSWERED{background:var(--amber);border-color:#ffe08a;color:#6d5200;font-weight:600}
.st-RESOLVED{background:var(--green);border-color:#b7e1c5;color:#1e6b3a;font-weight:600}
.st-BLOCKED{background:var(--red);border-color:#f0a6a6;color:#8a1212;font-weight:600}
.st-DONE{background:var(--green);border-color:#b7e1c5;color:#1e6b3a;font-weight:600}
.pill{display:inline-block;border:1px solid;border-radius:99px;padding:1px 8px;font-size:13px}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;
      padding:14px 16px;margin:14px 0}
.card.question{background:var(--amber);border-color:#ffe08a}
.card.answer{background:#fff;border-width:2px;border-color:var(--blue)}
.card.issue{background:var(--red);border-color:#f0a6a6}
.card h2:first-child{margin-top:0}
.note{color:var(--mut);font-size:13px}
figure{margin:12px 0;background:#fff;border:1px solid var(--line);border-radius:10px;padding:10px}
figure img{max-width:100%;height:auto;display:block;border:1px solid #eceff3}
figcaption{font-size:12.5px;color:var(--mut);margin-top:7px}
table{border-collapse:collapse;background:#fff;width:100%;font-size:14px;margin:10px 0}
th,td{border:1px solid var(--line);padding:7px 10px;text-align:left;vertical-align:top}
th{background:#eef1f5}
td.pages{white-space:nowrap}
ol.steps{padding-left:1.3em}
textarea{width:100%;min-height:150px;font:14px/1.5 ui-monospace,Consolas,monospace;
         border:1px solid var(--line);border-radius:8px;padding:10px;background:#fff}
.handwrite{display:none}
.handwrite .rule{border-bottom:1px solid #9aa4b1;height:2.1em;margin:0 0 .2em}
.warn{background:var(--red);border:1px solid #f0a6a6;border-radius:8px;padding:10px 12px}
ul.plain{list-style:none;padding-left:0}
footer{margin-top:26px;border-top:1px solid var(--line);padding-top:10px;
       color:var(--mut);font-size:12.5px}
@media print{
  body{max-width:none;background:#fff;padding:0}
  textarea,.noprint{display:none!important}
  .handwrite{display:block}
  .card,figure,tr{break-inside:avoid}
  .card{border-color:#999}
  a{color:#000;text-decoration:none}
}
"""


# --------------------------------------------------------------------------- #
# parsers
# --------------------------------------------------------------------------- #

def parse_query(path: Path) -> dict:
    """Query markdown -> {id, title, status, chunk, sections, text}."""
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    first = lines[0] if lines else ""
    if not TITLE_RE.match(first) or not STATUS_RE.search(first):
        raise ValueError(f"{path.name}: first line must be '# Q-NNN … [OPEN]'")
    title = STATUS_RE.sub("", TITLE_RE.match(first).group(1)).strip()
    title = re.sub(r"^(Q-\d+)\s+", "", title)      # id is rendered separately
    status = STATUS_RE.search(first).group(1)
    qid = QUERY_MARK_RE.search(first).group(0) if QUERY_MARK_RE.search(first) else path.stem

    sections: dict[str, str] = {}
    current, buf = None, []
    for line in lines[1:]:
        m = HEADING_RE.match(line)
        if m:
            if current is not None:
                sections[current] = "\n".join(buf).strip()
            current, buf = m.group(1), []
        elif current is not None:
            buf.append(line)
    if current is not None:
        sections[current] = "\n".join(buf).strip()

    head = sections.get("Chunk + PDF ref", "")
    m = CHUNK_REF_RE.search(head) or CHUNK_REF_RE.search(text)
    return {"id": qid, "title": title, "status": status,
            "chunk": m.group(1) if m else None,
            "sections": sections, "text": text, "file": path.name}


def parse_chunk(path: Path) -> dict:
    """Chunk YAML subset: flat keys plus `key: |` block scalars (no PyYAML)."""
    record: dict = {"_file": path.name}
    lines = path.read_text(encoding="utf-8").splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.strip() and not line.startswith((" ", "\t", "#")):
            m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):\s*(.*)$", line)
            if m:
                key, rest = m.group(1), m.group(2).strip()
                if rest in ("|", "|-", "|+", ">", ">-", ">+"):
                    block, i = [], i + 1
                    while i < len(lines) and (not lines[i].strip()
                                              or lines[i].startswith((" ", "\t"))):
                        block.append(lines[i][2:] if lines[i][:2] == "  " else "")
                        i += 1
                    record[key] = "\n".join(block).strip("\n")
                    continue
                record[key] = rest.strip('"')
        i += 1
    return record


def chunk_classes(rec: dict) -> list[tuple[str, str]]:
    """F1–F4 classification paragraphs from the `author_steps` block."""
    lines = rec.get("author_steps", "").splitlines()
    out: list[tuple[str, str]] = []
    for idx, line in enumerate(lines):
        indent = len(line) - len(line.lstrip())
        if indent or not CLASS_MARK_RE.match(line):
            continue
        para = [line.strip()]
        for nxt in lines[idx + 1:]:
            nxt_indent = len(nxt) - len(nxt.lstrip())
            if nxt.strip() and nxt_indent <= indent:
                break
            if nxt.strip():
                para.append(nxt.strip())
        out.append((f"F{CLASS_MARK_RE.match(line.strip()).group(1)}", " ".join(para)))
    return out


def chunk_queries(rec: dict) -> list[str]:
    return sorted(set(QUERY_MARK_RE.findall(rec.get("author_steps", ""))))


def page_list(rec: dict | None) -> str:
    if not rec:
        return "—"
    raw = str(rec.get("pdf_pages", "")).strip()
    return raw.strip("[]") if raw else "—"


# --------------------------------------------------------------------------- #
# markdown -> html (subset: headings, fences, lists, quotes, links, code)
# --------------------------------------------------------------------------- #

def _rel(target: Path, start: Path) -> str:
    """Relative URL from directory `start` to file `target`."""
    return Path(os.path.relpath(target, start)).as_posix()


def _code_span(escaped: str, base: Path) -> str:
    """`code` -> <code>, wrapped in a link when it names an existing repo file."""
    if PATH_REF_RE.fullmatch(escaped) and (ROOT / escaped).exists():
        return f'<a href="{html.escape(_rel(ROOT / escaped, base), quote=True)}">' \
               f"<code>{escaped}</code></a>"
    return f"<code>{escaped}</code>"


def _inline(segment: str, base: Path) -> str:
    """Bold, links and inline code inside an already-escaped segment."""
    def sub_code(m: re.Match) -> str:
        return _code_span(m.group(1), base)

    # protect code spans first so bold/link regexes cannot touch them
    parts = re.split(r"(`[^`]+`)", segment)
    for i, part in enumerate(parts):
        if part.startswith("`") and part.endswith("`") and len(part) > 2:
            parts[i] = sub_code(re.match(r"`(.*)`", part, re.S))
        else:
            def sub_link(m: re.Match, _p=part) -> str:
                label, target = m.group(1), m.group(2)
                if target.startswith(("http://", "https://", "#")):
                    return f'<a href="{html.escape(target, quote=True)}">{label}</a>'
                if (ROOT / target).exists():
                    return f'<a href="{html.escape(_rel(ROOT / target, base), quote=True)}">' \
                           f"{label}</a>"
                return label

            part = re.sub(r"\[([^\]]+)\]\(([^)\s]+)\)", sub_link, part)
            part = re.sub(r"\*\*([^*]+)\*\*", r"<b>\1</b>", part)
            parts[i] = part
    return "".join(parts)


def md_to_html(text: str, base: Path) -> str:
    out: list[str] = []
    para: list[str] = []
    code_buf: list[str] | None = None
    list_mode: str | None = None

    def flush_para() -> None:
        if para:
            out.append("<p>" + _inline(" ".join(para), base) + "</p>")
            para.clear()

    def close_list() -> None:
        nonlocal list_mode
        if list_mode:
            out.append(f"</{list_mode}>")
            list_mode = None

    for raw in text.splitlines():
        line = raw.rstrip()
        if code_buf is not None:
            if line.strip().startswith("```"):
                out.append("<pre>" + html.escape("\n".join(code_buf)) + "</pre>")
                code_buf = None
            else:
                code_buf.append(raw)
            continue
        if line.strip().startswith("```"):
            flush_para()
            close_list()
            code_buf = []
            continue
        if not line.strip():
            flush_para()
            close_list()
            continue
        m = re.match(r"^(#{1,6})\s+(.*)$", line)
        if m:
            flush_para()
            close_list()
            lvl = min(len(m.group(1)) + 1, 6)      # query text is sub-headings
            out.append(f"<h{lvl}>{_inline(html.escape(m.group(2)), base)}</h{lvl}>")
            continue
        if line.startswith(">"):
            flush_para()
            close_list()
            out.append("<blockquote>" + _inline(html.escape(line.lstrip("> ")), base)
                       + "</blockquote>")
            continue
        if re.match(r"^\s*[-*]\s+", line):
            flush_para()
            if list_mode != "ul":
                close_list()
                out.append("<ul>")
                list_mode = "ul"
            item = re.sub(r"^\s*[-*]\s+", "", line)
            out.append("<li>" + _inline(html.escape(item), base) + "</li>")
            continue
        if re.match(r"^\s*\d+[.)]\s+", line):
            flush_para()
            if list_mode != "ol":
                close_list()
                out.append("<ol>")
                list_mode = "ol"
            item = re.sub(r"^\s*\d+[.)]\s+", "", line)
            out.append("<li>" + _inline(html.escape(item), base) + "</li>")
            continue
        close_list()
        para.append(html.escape(line))
    if code_buf is not None:
        out.append("<pre>" + html.escape("\n".join(code_buf)) + "</pre>")
    flush_para()
    close_list()
    return "\n".join(out)


# --------------------------------------------------------------------------- #
# page builders
# --------------------------------------------------------------------------- #

def figures_for(query: dict, rec: dict | None, base: Path) -> list[tuple[str, str]]:
    """(src, caption) for every image the query text or the chunk record names."""
    found: list[tuple[str, str]] = []
    for ref in IMAGE_REF_RE.findall(query["text"]):
        cand = ROOT / ref if ref.startswith("pipeline/") else HERE / ref
        if not cand.exists():
            cand = RENDER_DIR / Path(ref).name
        if cand.exists():
            found.append((_rel(cand, base),
                          f"{query['id']} evidence — {Path(ref).name}"))
    if rec:
        for render in str(rec.get("renders", "")).split():
            cand = RENDER_DIR / render
            if cand.exists():
                found.append((_rel(cand, base),
                              f"{rec.get('id', 'chunk')} — PDF page(s) "
                              f"{page_list(rec)}, render {render}"))
    uniq, done = [], set()
    for src, cap in found:
        if src not in done:
            done.add(src)
            uniq.append((src, cap))
    return uniq


def question_lead(query: dict) -> str:
    body = query["sections"].get("Question for the author", "")
    m = re.search(r"^(?P<p>.*?)\n\s*\n", body, re.S)
    lead = (m.group("p") if m else body).strip()
    return lead or "(question text missing)"


def build_issue_page(query: dict, rec: dict | None, out_dir: Path) -> str:
    chunk_id = query["chunk"] or "—"
    decls = [d.strip() for d in str(rec.get("lean_decls", "")).split(",") if d.strip()] \
        if rec else []

    class_html = ""
    classes = chunk_classes(rec) if rec else []
    if classes:
        items = "".join(f"<li><b>{cls}</b> — {md_to_html(para, out_dir)}</li>"
                        for cls, para in classes)
        class_html = (
            '<div class="card"><h2>Ghi chú phân loại / Classification notes '
            "(internal)</h2><ul>" + items + "</ul>"
            '<p class="note">F3 = a gap we filled from your own material (no new '
            "assumption). F4 = a proof step Lean could not verify; it needs your "
            "answer above.</p></div>")

    figs = figures_for(query, rec, out_dir)
    fig_html = ""
    if figs:
        blocks = "".join(
            f'<figure><img src="{html.escape(src, quote=True)}" alt="{html.escape(cap)}" '
            f'loading="lazy"><figcaption>{html.escape(cap)} — '
            f'<a href="{html.escape(src, quote=True)}">open full size</a></figcaption></figure>'
            for src, cap in figs)
        fig_html = ('<div class="card"><h2>Trang in / The printed pages '
                    "(bản in là căn cứ — the print is authoritative)</h2>" + blocks + "</div>")

    review_html = ""
    if REVIEW_DIR.exists():
        review_html = (f'<p class="note">Bản xem xét / review display: '
                       f'<a href="{html.escape(_rel(REVIEW_DIR / "index.html", out_dir), quote=True)}">'
                       f"01-extract/out/review/index.html</a> — open the same page "
                       f"there to compare the print with the extract.</p>")

    question_card = (
        '<div class="card question"><h2>❓ Câu hỏi dành cho tác giả / '
        "Question for the author</h2>"
        + md_to_html(question_lead(query), out_dir)
        + f'<p class="note">Trả lời ở cuối trang / reply at the bottom of this page, '
          f'or edit <code>reply-{query["id"]}.md</code> and send it back.</p></div>')

    # sections rendered in their own cards above; the rest keep their own titles
    in_card = {"Question for the author", "Chunk + PDF ref",
               "What we formalized", "What failed"}
    body_parts = [
        f"<h3>{html.escape(name)}</h3>" + md_to_html(body, out_dir)
        for name, body in query["sections"].items()
        if name not in in_card and body.strip()]

    decl_html = ""
    if decls:
        decl_html = ("<h3>Đã kiểm chứng trong Lean / verified declarations</h3><ul class='plain'>"
                     + "".join(f"<li><code>{html.escape(d)}</code></li>" for d in decls)
                     + "</ul>")

    return f"""<!doctype html>
<html lang="vi">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(query['id'])} — {html.escape(query['title'])}</title>
<style>{STYLE}</style>
</head>
<body>
<p class="noprint"><a href="index.html">← Danh mục / report index</a></p>
<h1>{html.escape(query['id'])} · {html.escape(query['title'])}</h1>
<div class="chips">
  <span class="st-{query['status']}">{query['status']}</span>
  <span><b>chunk</b> {html.escape(chunk_id)}</span>
  <span><b>PDF pages</b> {html.escape(page_list(rec))}</span>
  <span><b>decls</b> {len(decls)}</span>
  <span><b>file</b> {html.escape(query['file'])}</span>
</div>
{question_card}
<div class="card issue">
<h2>⚠ Vấn đề / What Lean could not verify</h2>
{md_to_html(query['sections'].get('What failed', '(section missing)'), out_dir)}
</div>
<div class="card">
<h2>Bản in nói gì / What the print says</h2>
{md_to_html(query['sections'].get('Chunk + PDF ref', '(section missing)'), out_dir)}
{review_html}
</div>
{fig_html}
<div class="card">
<h2>Phát biểu đã kiểm chứng / What we formalized (the statement Lean checks)</h2>
{md_to_html(query['sections'].get('What we formalized', '(section missing)'), out_dir)}
{decl_html}
</div>
{''.join(body_parts)}
{class_html}
<div class="card answer">
<h2>✍️ Trả lời của tác giả / Author's reply</h2>
<p class="note">Gõ vào ô dưới đây rồi copy vào email, hoặc sửa tệp
<code>reply-{html.escape(query['id'])}.md</code>. / Type below and paste into an
email, or edit the reply template file.</p>
<textarea spellcheck="false" placeholder="{html.escape(query['id'])}: câu trả lời của quý vị / your answer …"></textarea>
<div class="handwrite">
  <p class="note">In trang này và viết tay / print this page and write by hand:</p>
  <div class="rule"></div><div class="rule"></div><div class="rule"></div>
  <div class="rule"></div><div class="rule"></div><div class="rule"></div>
</div>
</div>
<footer>
Sinh từ / generated by <code>pipeline/05-feedback/render_report.py</code> on
{datetime.date.today().isoformat()} — nguồn / sources:
<code>{html.escape(query['file'])}</code>{f", <code>{html.escape(rec['_file'])}</code>" if rec else ""}.
Không cần Lean để trả lời / no Lean required to answer.
</footer>
</body>
</html>
"""


def build_index(queries: list[dict], recs: dict[str, dict], warnings: list[str],
                out_dir: Path) -> str:
    rows = []
    for q in queries:
        rec = recs.get(q["chunk"] or "")
        rows.append(
            "<tr>"
            f'<td><a href="{q["id"]}.html"><b>{html.escape(q["id"])}</b></a></td>'
            f"<td>{html.escape(q['title'])}</td>"
            f'<td><span class="pill st-{q["status"]}">{q["status"]}</span></td>'
            f"<td>{html.escape(q['chunk'] or '—')}</td>"
            f'<td class="pages">{html.escape(page_list(rec))}</td>'
            f'<td><a href="reply-{q["id"]}.md">reply template</a></td>'
            "</tr>")

    chunk_rows = []
    for cid in sorted(recs):
        rec = recs[cid]
        decls = [d for d in str(rec.get("lean_decls", "")).split(",") if d.strip()]
        status = str(rec.get("status", "?"))
        links = ", ".join(f'<a href="{q}.html">{q}</a>' for q in chunk_queries(rec)) or "—"
        chunk_rows.append(
            "<tr>"
            f"<td><b>{html.escape(cid)}</b></td>"
            f'<td><span class="pill st-{status}">{status}</span></td>'
            f"<td>{html.escape(page_list(rec))}</td>"
            f"<td>{len(decls)} decls</td>"
            f"<td>{links}</td>"
            "</tr>")

    warn_html = ""
    if warnings:
        warn_html = ('<div class="warn"><b>Ghi chú kỹ thuật / internal checks '
                     "(report may be incomplete)</b><ul>"
                     + "".join(f"<li>{html.escape(w)}</li>" for w in warnings)
                     + "</ul></div>")

    open_q = sum(1 for q in queries if q["status"] == "OPEN")
    blocked = [c for c, r in recs.items() if str(r.get("status")) == "BLOCKED"]
    review_html = ""
    if REVIEW_DIR.exists():
        review_html = (f'<p class="note">Bản xem xét / review display: '
                       f'<a href="{html.escape(_rel(REVIEW_DIR / "index.html", out_dir), quote=True)}">'
                       f"01-extract/out/review/index.html</a></p>")

    return f"""<!doctype html>
<html lang="vi">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Báo cáo kiểm chứng / verification report</title>
<style>{STYLE}</style>
</head>
<body>
<h1>Báo cáo kiểm chứng — các câu hỏi dành cho tác giả</h1>
<p class="note">Verification report — open questions for the author
(generated {datetime.date.today().isoformat()}; no Lean needed to answer).</p>
<div class="chips">
  <span><b>câu hỏi / queries</b> {len(queries)} ({open_q} OPEN)</span>
  <span class="pill st-BLOCKED">BLOCKED chunks: {len(blocked)}</span>
  <span><b>chunks in ledger</b> {len(recs)}</span>
</div>
{warn_html}
<div class="card question">
<h2>Cách trả lời / How to respond</h2>
<ol class="steps">
<li>Mở trang câu hỏi / open the query page (link in the table below).</li>
<li>Đọc “Câu hỏi dành cho tác giả” — mỗi trang có một câu hỏi duy nhất
    (một dòng sai trong bản in, hoặc một bước chứng minh không suy ra được).</li>
<li>Trả lời: gõ vào ô <i>Trả lời của tác giả</i> ở cuối trang rồi copy vào email,
    hoặc sửa tệp <code>reply-Q-NNN.md</code>.</li>
<li>Nếu phải đính chính bản in, ghi rõ số trang và dòng; bản in là căn cứ.
    Trang render của từng trang PDF nằm ngay trong trang câu hỏi.</li>
</ol>
</div>
<h2>Câu hỏi / Queries</h2>
<table>
<tr><th>ID</th><th>Title</th><th>Status</th><th>Chunk</th><th>PDF pages</th><th>Reply</th></tr>
{''.join(rows)}
</table>
<h2>Trạng thái từng bổ đề / Chunk status</h2>
<table>
<tr><th>Chunk</th><th>Status</th><th>Pages</th><th>Lean</th><th>Queries</th></tr>
{''.join(chunk_rows)}
</table>
{review_html}
<footer>
Sinh bởi / generated by <code>pipeline/05-feedback/render_report.py</code>;
nguồn sự thật / sources of truth: <code>pipeline/05-feedback/queries/</code> and
<code>pipeline/02-chunks/chunks/</code>. Do not edit generated files by hand.
</footer>
</body>
</html>
"""


def build_reply(query: dict, rec: dict | None) -> str:
    lead = re.sub(r"[ \t]+\n", "\n", question_lead(query))
    return f"""# {query['id']} — trả lời của tác giả / author reply

- câu hỏi / question: {query['title']}
- chunk: {query['chunk'] or '?'}   PDF trang / pages: {page_list(rec)}
- trạng thái / status: {query['status']}

## Câu hỏi / Question

{lead}

## Trả lời / Answer

(your answer here — one sentence is enough when the correction is a sign, a
number, or a line reference)

## Đính chính bản in / Correction to the printed text (if any)

- trang / page:
- dòng / line:
- chữ đúng / correct text:

## Chữ ký / Signature

- họ tên / name:
- ngày / date:
"""


# --------------------------------------------------------------------------- #
# consistency checks
# --------------------------------------------------------------------------- #

def check(queries: list[dict], recs: dict[str, dict]) -> list[str]:
    warnings: list[str] = []
    query_ids = {q["id"] for q in queries}
    for q in queries:
        if q["chunk"] is None:
            warnings.append(f"{q['id']}: no chunk reference found")
        elif q["chunk"] not in recs:
            warnings.append(f"{q['id']}: references unknown chunk {q['chunk']}")
        for ref in IMAGE_REF_RE.findall(q["text"]):
            cand = ROOT / ref if ref.startswith("pipeline/") else HERE / ref
            if not cand.exists() and not (RENDER_DIR / Path(ref).name).exists():
                warnings.append(f"{q['id']}: image not found: {ref}")

    by_chunk: dict[str, list[str]] = {}
    for q in queries:
        if q["chunk"]:
            by_chunk.setdefault(q["chunk"], []).append(q["id"])
    for cid, rec in recs.items():
        if str(rec.get("status")) == "BLOCKED" and cid not in by_chunk:
            warnings.append(f"{cid}: BLOCKED but no author query references it")
        for qid in chunk_queries(rec):
            if qid not in query_ids:
                warnings.append(f"{cid}: mentions {qid}, but queries/{qid}-*.md is missing")
        for render in str(rec.get("renders", "")).split():
            if not (RENDER_DIR / render).exists():
                warnings.append(f"{cid}: render missing: {render}")
    return warnings


# --------------------------------------------------------------------------- #

def main() -> int:
    ap = argparse.ArgumentParser(description="author report for Lean findings")
    ap.add_argument("--out", default=str(DEFAULT_OUT), metavar="DIR",
                    help="output directory (default: %(default)s)")
    ap.add_argument("--quiet", action="store_true", help="only errors on stdout")
    args = ap.parse_args()

    query_files = sorted(p for p in QUERIES_DIR.glob("Q-*.md")
                         if "template" not in p.stem.lower())
    if not query_files:
        print(f"error: no queries in {QUERIES_DIR}", file=sys.stderr)
        return 1

    queries: list[dict] = []
    for path in query_files:
        try:
            queries.append(parse_query(path))
        except ValueError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1

    recs: dict[str, dict] = {}
    for path in sorted(CHUNKS_DIR.glob("*.yml")):
        rec = parse_chunk(path)
        if rec.get("id"):
            recs[rec["id"]] = rec
    warnings = check(queries, recs)

    out_dir = Path(args.out)
    if not out_dir.is_absolute():
        out_dir = Path.cwd() / out_dir
    try:
        out_dir.mkdir(parents=True, exist_ok=True)
        for q in queries:
            rec = recs.get(q["chunk"] or "")
            (out_dir / f"{q['id']}.html").write_text(
                build_issue_page(q, rec, out_dir), encoding="utf-8")
            (out_dir / f"reply-{q['id']}.md").write_text(
                build_reply(q, rec), encoding="utf-8")
        (out_dir / "index.html").write_text(
            build_index(queries, recs, warnings, out_dir), encoding="utf-8")
    except OSError as exc:
        print(f"error: cannot write report: {exc}", file=sys.stderr)
        return 2

    if not args.quiet:
        print(f"report: {len(queries)} queries -> {out_dir / 'index.html'}")
        for q in queries:
            print(f"  {q['id']:<8} {q['status']:<9} chunk={q['chunk'] or '-':<12} "
                  f"{out_dir / (q['id'] + '.html')}")
        for w in warnings:
            print(f"  warning: {w}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
