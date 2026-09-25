"""Vision-LaTeX region extraction: admission gate, split planning, gates, signoff.

Usage:
    python regions.py precheck [--check-answer | --fixture PAGE=PATH ...] [--pages SPEC]
    python regions.py words <pdf> <page>
    python regions.py plan <pdf> <page> --spec <json|file> [--out FILE]
    python regions.py verify <record.yml>
    python regions.py signoff <record.yml>
    python regions.py status [--pages SPEC]
    python regions.py export <record.yml> ... --out <file.tex>

Stage admission: `plan` refuses to run unless `out/vision-probe.pass`
admits the page — either the vision probe passed (a vision-capable
session transcribed out/vision-probe.png and --check-answer verified
it) or the user supplied LaTeX fixtures covering the page
(`precheck --fixture <page>=<path> --pages <spec>`). Without vision
and without fixtures the stage STOPS; that is by design: no other
input can carry the PDF's 2-D math faithfully.

Splitting guidance (the only prose guidance in this stage — the gates
check the result):
  - split at gaps between display equations; horizontal bands preferred;
  - on 2-column pages split columns first;
  - never cut a formula;
  - 1-12 regions per page.

Record layout (pipeline/01-extract/regions/pNNN.yml): flat header
(id, page, source_pdf_sha, status DRAFT|REVIEWED, signed_latex_sha256,
signed_on) + `regions:` list of {id, rect, crop, words, digits_sorted,
pua, notes, latex}. Each `latex:` block holds the region's content as
complete display math WITH delimiters (\\[ ... \\], $$...$$, or a full
environment like align*); one block may contain several display groups;
printed `*` bullets are transcribed `\\text{*}\\;` at line start;
`\\textcolor{...}{...}` and `\\mathbf` carry the green/red/bold
emphasis visible in the render. Ambiguities go in `notes`.

Exit codes: 0 success / gate green; 1 gate failure (message on stdout);
2 usage error or precheck awaiting answer.
"""

import argparse
import hashlib
import json
import re
import sys
import unicodedata
from collections import Counter
from datetime import date
from pathlib import Path

# Local sibling modules (render_pdf, fidelity_check) must be importable
# when regions.py is loaded from elsewhere (progress.py uses spec_from_file_location).
_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

import pymupdf  # noqa: E402  (pinned in requirements-container.txt)

OUT_DIR = _HERE / "out"
REGIONS_DIR = _HERE / "regions"
ROOT = _HERE.parent.parent
PASS_FILE = OUT_DIR / "vision-probe.pass"
PROBE_TEXT = "f'(b^2)=73+h^{n-1}"
MIN_REGION_HEIGHT = 60.0
MIN_REGION_WIDTH = 120.0
MAX_REGIONS = 12
EPS = 1e-6
REGION_DPI = 300
# Symbol-font superscripts: pymupdf emits printed digit k as U+F030+k (a
# Private-Use glyph), so a plain '0'..'9' filter silently drops digits the
# render shows (found on pp.16/18/19/22/25/26/29/30 superscript exponents).
PUA_DIGIT_BASE = 0xF030


def word_digit_chars(text: str) -> list[str]:
    """ASCII digits plus PUA-encoded digit glyphs (U+F030+k -> digit k)."""
    decoded = "".join(
        chr(0x30 + ord(ch) - PUA_DIGIT_BASE)
        if PUA_DIGIT_BASE <= ord(ch) <= PUA_DIGIT_BASE + 9 else ch
        for ch in text)
    return [ch for ch in decoded if "0" <= ch <= "9"]


# ---------------------------------------------------------------- utilities

def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_answer(text: str) -> str:
    """Canonical form for probe answers: unicode-fold, drop math decoration.

    NFC; primes/backticks to ASCII apostrophe; unicode dashes to '-';
    delete whitespace, braces, dollar signs, backslashes and brackets so
    that LaTeX-wrapped or brace-style answers compare equal.
    """
    t = unicodedata.normalize("NFC", text)
    t = t.replace("′", "'").replace("`", "'")
    t = t.replace("−", "-").replace("–", "-").replace("—", "-")
    for ch in " \t\r\n{}$\\[]":
        t = t.replace(ch, "")
    return t


def probe_sha() -> str:
    return hashlib.sha256(normalize_answer(PROBE_TEXT).encode("utf-8")).hexdigest()


def parse_page_spec(raw: str) -> list[int]:
    """'1-33' / '3,7' / '3,5-7' -> sorted unique page numbers."""
    pages: list[int] = []
    for part in raw.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            lo, hi = part.split("-", 1)
            pages.extend(range(int(lo), int(hi) + 1))
        else:
            pages.append(int(part))
    if not pages:
        raise ValueError(f"empty page spec: {raw!r}")
    return sorted(set(pages))


def read_pass() -> dict | None:
    if not PASS_FILE.is_file():
        return None
    data: dict = {}
    for line in PASS_FILE.read_text(encoding="utf-8").splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            data[key] = value
    return data or None


def write_pass(lines: list[str]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    PASS_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def page_admitted(page: int) -> bool:
    state = read_pass()
    if not state:
        return False
    if state.get("mode") == "probe":
        return state.get("expected_sha256") == probe_sha()
    if state.get("mode") == "fixtures":
        listed = {int(x) for x in state.get("pages", "").split(",") if x.strip()}
        return page in listed
    return False


def admit_or_die(page: int) -> int | None:
    """Return None if admitted, else the exit code to return (message printed)."""
    if page_admitted(page):
        return None
    print("precheck not passed (run regions.py precheck)")
    return 1


# ------------------------------------------------------------ record parse/write

def _scalar(value: str):
    """Parse the right-hand side of a flat/region key line."""
    if value == '""':
        return ""
    if len(value) >= 2 and value.startswith('"') and value.endswith('"'):
        inner = value[1:-1]
        return inner.replace('\\"', '"').replace("\\\\", "\\")
    if value.startswith("[") and value.endswith("]"):
        items = [v.strip() for v in value[1:-1].split(",") if v.strip()]
        try:
            return [float(v) for v in items]
        except ValueError:
            return items
    return value


def load_page_record(path: Path) -> dict:
    """Hand-rolled YAML subset reader (container has no PyYAML; repo convention).

    Flat `key: value` header + `regions:` list of `  - key: value` items
    with `latex: |` block scalars (content = lines indented past the
    4-space key indent, dedented, trailing blank lines stripped).
    """
    if not path.is_file():
        raise FileNotFoundError(f"missing region record: {path}")
    record: dict = {"regions": []}
    lines = path.read_text(encoding="utf-8").splitlines()
    i = 0
    current: dict | None = None
    while i < len(lines):
        line = lines[i]
        if not line.strip() or line.lstrip().startswith("#"):
            i += 1
            continue
        if not line[0].isspace():          # top-level flat key
            key, _, value = line.partition(":")
            if key.strip() != "regions":   # list header: never overwrite the list
                record[key.strip()] = _scalar(value.strip())
            current = None
            i += 1
            continue
        if line.startswith("  - "):         # new region item
            key, _, value = line[4:].partition(":")
            current = {key.strip(): _scalar(value.strip())}
            record["regions"].append(current)
            i += 1
            continue
        if current is None:                # stray indent (e.g. continuation)
            i += 1
            continue
        body = line[4:]
        key, sep, value = body.partition(":")
        if not sep:
            i += 1
            continue
        value = value.strip()
        if value == "|":                   # block scalar
            block: list[str] = []
            base: int | None = None
            j = i + 1
            while j < len(lines):
                ln = lines[j]
                if not ln.strip():
                    block.append("")
                    j += 1
                    continue
                indent = len(ln) - len(ln.lstrip())
                if indent < 5:
                    break
                if base is None:
                    base = indent
                block.append(ln[base:] if indent >= base else ln.lstrip())
                j += 1
            while block and not block[-1]:
                block.pop()
            current[key.strip()] = "\n".join(block)
            i = j
            continue
        current[key.strip()] = _scalar(value)
        i += 1
    if "regions" not in record:
        record["regions"] = []
    return record


def latex_aggregate(record: dict) -> str:
    """All latex blocks concatenated verbatim in region order (no separator)."""
    return "".join(region.get("latex", "") for region in record["regions"])


def record_fresh(record: dict) -> bool:
    if record.get("status") != "REVIEWED":
        return False
    stored = record.get("signed_latex_sha256", "")
    return bool(stored) and hashlib.sha256(
        latex_aggregate(record).encode("utf-8")).hexdigest() == stored


def review_rows(record: dict) -> list[dict]:
    """Per-region rows for the review surface: id, crop, latex, flags.

    Flags: 'digit mismatch' (latex digits != stored audit), 'PUA n'
    (engine garbage at plan time), 'notes', 'stale signoff' (record-level:
    REVIEWED but latex edited after signoff -> applies to every row).
    """
    rows = []
    stale = record.get("status") == "REVIEWED" and not record_fresh(record)
    for index, region in enumerate(record.get("regions", []), 1):
        flags = []
        if latex_digits(str(region.get("latex", ""))) != str(region.get("digits_sorted", "")):
            flags.append("digit mismatch")
        try:
            pua = int(region.get("pua", 0) or 0)
        except (TypeError, ValueError):
            pua = 0
        if pua > 0:
            flags.append(f"PUA {pua}")
        if str(region.get("notes", "")).strip():
            flags.append("notes")
        if stale:
            flags.append("stale signoff")
        rows.append({
            "id": str(region.get("id", f"R{index}")),
            "crop": str(region.get("crop", "")),
            "latex": str(region.get("latex", "")),
            "flags": flags,
        })
    return rows


# ------------------------------------------------------------- geometry gates

def _inside(rect: list[float], outer) -> bool:
    return (rect[0] >= outer[0] - EPS and rect[1] >= outer[1] - EPS
            and rect[2] <= outer[2] + EPS and rect[3] <= outer[3] + EPS)


def _interiors_overlap(a: list[float], b: list[float]) -> bool:
    return (a[0] < b[2] - EPS and b[0] < a[2] - EPS
            and a[1] < b[3] - EPS and b[1] < a[3] - EPS)


def _cell_covered(rect: list[float], cell: list[float]) -> bool:
    return (rect[0] <= cell[0] + EPS and rect[1] <= cell[1] + EPS
            and rect[2] >= cell[2] - EPS and rect[3] >= cell[3] - EPS)


def _sweep_uncovered(rects: list[list[float]], outer) -> list[list[float]]:
    """Elementary cells of the edge grid, inside `outer`, covered by no rect."""
    xs = sorted({round(v, 6) for r in rects for v in (r[0], r[2])} | {round(outer[0], 6), round(outer[2], 6)})
    ys = sorted({round(v, 6) for r in rects for v in (r[1], r[3])} | {round(outer[1], 6), round(outer[3], 6)})
    uncovered = []
    for xi in range(len(xs) - 1):
        for yi in range(len(ys) - 1):
            cell = [xs[xi], ys[yi], xs[xi + 1], ys[yi + 1]]
            if not _inside(cell, outer):
                continue
            if not any(_cell_covered(r, cell) for r in rects):
                uncovered.append(cell)
    return uncovered


def geometry_errors(regions: list[dict], page_rect) -> list[str]:
    """Plan-time gates: count/size/containment/disjointness/exact coverage."""
    errors: list[str] = []
    if not 1 <= len(regions) <= MAX_REGIONS:
        errors.append(f"region count {len(regions)} outside 1-{MAX_REGIONS}")
    outer = [page_rect.x0, page_rect.y0, page_rect.x1, page_rect.y1]
    for region in regions:
        rect = region["rect"]
        width, height = rect[2] - rect[0], rect[3] - rect[1]
        if width < MIN_REGION_WIDTH - EPS:
            errors.append(f"{region['id']}: width {width:.1f}pt < {MIN_REGION_WIDTH:.0f}pt")
        if height < MIN_REGION_HEIGHT - EPS:
            errors.append(f"{region['id']}: height {height:.1f}pt < {MIN_REGION_HEIGHT:.0f}pt")
        if not _inside(rect, outer):
            errors.append(f"{region['id']}: rect {rect} outside page {outer}")
    for i in range(len(regions)):
        for j in range(i + 1, len(regions)):
            if _interiors_overlap(regions[i]["rect"], regions[j]["rect"]):
                errors.append(f"{regions[i]['id']} overlaps {regions[j]['id']}")
    if not any("overlaps" in e for e in errors):
        for cell in _sweep_uncovered([r["rect"] for r in regions], outer):
            errors.append(f"uncovered cell [{cell[0]:.1f}, {cell[1]:.1f}, "
                          f"{cell[2]:.1f}, {cell[3]:.1f}]")
    return errors


def tiling_errors(rects: list[list[float]]) -> list[str]:
    """Verify-time: stored rects must tile one rectangle (disjoint + covered)."""
    errors: list[str] = []
    for i in range(len(rects)):
        for j in range(i + 1, len(rects)):
            if _interiors_overlap(rects[i], rects[j]):
                errors.append(f"rect {i + 1} overlaps rect {j + 1}")
    if rects and not any("overlaps" in e for e in errors):
        outer = [min(r[0] for r in rects), min(r[1] for r in rects),
                 max(r[2] for r in rects), max(r[3] for r in rects)]
        for cell in _sweep_uncovered(rects, outer):
            errors.append(f"uncovered cell [{cell[0]:.1f}, {cell[1]:.1f}, "
                          f"{cell[2]:.1f}, {cell[3]:.1f}]")
    return errors


# ------------------------------------------------------------- latex checks

def strip_comments(text: str) -> str:
    """Remove unescaped % comments to end of line."""
    out = []
    for line in text.splitlines():
        buf, i = [], 0
        while i < len(line):
            ch = line[i]
            if ch == "\\" and i + 1 < len(line):
                buf.append(line[i:i + 2])
                i += 2
                continue
            if ch == "%":
                break
            buf.append(ch)
            i += 1
        out.append("".join(buf))
    return "\n".join(out)


def balance_errors(text: str) -> list[str]:
    t = strip_comments(text)
    errors = []
    depth, i = 0, 0
    while i < len(t):
        ch = t[i]
        if ch == "\\":
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth < 0:
                errors.append("unbalanced '}' (closing without opening)")
                depth = 0
        i += 1
    if depth > 0:
        errors.append(f"unbalanced '{{' ({depth} unclosed)")
    begins = Counter(re.findall(r"\\begin\{([^{}]*)\}", t))
    ends = Counter(re.findall(r"\\end\{([^{}]*)\}", t))
    if begins != ends:
        errors.append(f"environment mismatch: begin {dict(begins)} end {dict(ends)}")
    dollars = t.replace("\\$", "").count("$")
    if dollars % 2:
        errors.append(f"unpaired $ ({dollars} occurrences)")
    if t.count("\\[") != t.count("\\]"):
        errors.append(f"unpaired \\[\\] (\\[={t.count(chr(92) + '[')} "
                      f"\\]={t.count(chr(92) + ']')})")
    return errors


def _remove_group(t: str, start: int) -> str | None:
    """Drop the balanced {...} group whose '{' is at `start` (braces removed)."""
    depth, i = 0, start
    while i < len(t):
        ch = t[i]
        if ch == "\\":
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return t[:start] + t[i + 1:]
        i += 1
    return None  # unterminated: leave text; balance check reports it


def strip_digit_noise(text: str) -> str:
    """Drop comment lines + argument groups whose digits are NOT page content:
    \\label{} \\ref{} \\eqref{} \\tag{} (all args) and \\textcolor's color arg.
    """
    t = strip_comments(text)
    for cmd in ("\\label", "\\ref", "\\eqref", "\\tag"):
        while True:
            idx = t.find(cmd)
            if idx == -1:
                break
            brace = t.find("{", idx + len(cmd))
            if brace == -1:
                t = t[:idx] + t[idx + len(cmd):]
                continue
            removed = _remove_group(t, brace)
            if removed is None:
                break
            t = removed[:idx] + removed[idx + len(cmd):]
    while True:
        idx = t.find("\\textcolor")
        if idx == -1:
            break
        brace = t.find("{", idx + len("\\textcolor"))
        if brace == -1:
            t = t[:idx] + t[idx + len("\\textcolor"):]
            continue
        removed = _remove_group(t, brace)
        if removed is None:
            break
        t = removed[:idx] + removed[idx + len("\\textcolor"):]
    return t


def latex_digits(text: str) -> str:
    return "".join(sorted(c for c in strip_digit_noise(text) if "0" <= c <= "9"))


def stored_digits(record: dict) -> str:
    """Page total: every stored region digit, globally sorted (compared
    against latex_digits' globally sorted stream — per-region equality
    implies this, but it also catches corrupted digits_sorted fields)."""
    return "".join(sorted(
        ch for region in record.get("regions", [])
        for ch in str(region.get("digits_sorted", ""))))


def first_divergence(a: str, b: str) -> int:
    for i, (ca, cb) in enumerate(zip(a, b)):
        if ca != cb:
            return i
    return min(len(a), len(b))


# ------------------------------------------------------------- subcommands

def cmd_precheck(args) -> int:
    fixtures: dict[int, Path] = {}
    for item in args.fixture:
        if "=" not in item:
            print(f"bad --fixture {item!r}: expected PAGE=PATH")
            return 2
        page_s, path_s = item.split("=", 1)
        path = Path(path_s)
        if not path.is_file():
            path = ROOT / path_s
        fixtures[int(page_s)] = path

    if fixtures:
        pages = parse_page_spec(args.pages)
        missing = [p for p in pages
                   if p not in fixtures or not fixtures[p].is_file()]
        if missing:
            print(f"vision model required: pages {','.join(str(p) for p in missing)} lack fixtures")
            return 1
        write_pass(["mode=fixtures", "pages=" + ",".join(str(p) for p in pages)])
        print(f"fixture-admitted: pages {','.join(str(p) for p in pages)}")
        return 0

    if args.check_answer:
        answer_path = OUT_DIR / "vision-probe.answer.txt"
        if not answer_path.is_file():
            print("answer file missing: out/vision-probe.answer.txt")
            return 1
        got = normalize_answer(answer_path.read_text(encoding="utf-8"))
        want = normalize_answer(PROBE_TEXT)
        if got != want:
            print("vision probe mismatch")
            print(f"expected: {want}")
            print(f"answer:   {got}")
            return 1
        write_pass(["mode=probe", f"expected_sha256={probe_sha()}"])
        print("vision probe passed")
        return 0

    state = read_pass()
    if state and state.get("mode") == "probe" and state.get("expected_sha256") == probe_sha():
        print("precheck already passed (mode=probe)")
        return 0
    # render the synthetic probe: one page of exact text the answer must match
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    document = pymupdf.open()
    probe_page = document.new_page(width=612, height=792)
    probe_page.insert_text((72, 200), PROBE_TEXT, fontsize=24, fontname="cour")
    pixmap = probe_page.get_pixmap(dpi=150, colorspace=pymupdf.csRGB, alpha=False)
    (OUT_DIR / "vision-probe.png").write_bytes(pixmap.tobytes("png"))
    document.close()
    (OUT_DIR / "vision-probe.expected.txt").write_text(PROBE_TEXT + "\n", encoding="utf-8")
    print("awaiting vision answer")
    print("transcribe out/vision-probe.png to out/vision-probe.answer.txt "
          "then run: regions.py precheck --check-answer")
    return 2


def cmd_words(args) -> int:
    with pymupdf.open(args.pdf) as document:
        page = document[args.page - 1]
        for x0, y0, x1, y1, word, *_rest in page.get_text("words"):
            print(f"{x0:.1f} {y0:.1f} {x1:.1f} {y1:.1f} {word}")
    return 0


def load_spec(raw: str) -> list[dict]:
    path = Path(raw)
    text = path.read_text(encoding="utf-8") if path.is_file() else raw
    try:
        data = json.loads(text)
    except json.JSONDecodeError as exc:
        raise ValueError(f"spec is not valid JSON: {exc}") from exc
    if not isinstance(data, list) or not data:
        raise ValueError("spec must be a non-empty JSON array of {id, rect} entries")
    regions, seen = [], set()
    for item in data:
        if not isinstance(item, dict) or "id" not in item or "rect" not in item:
            raise ValueError("each spec item needs 'id' and 'rect'")
        rid = str(item["id"]).strip()
        if not rid or rid in seen:
            raise ValueError(f"duplicate or empty region id: {rid!r}")
        seen.add(rid)
        rect = item["rect"]
        if not isinstance(rect, list) or len(rect) != 4:
            raise ValueError(f"{rid}: rect must be [x0, y0, x1, y1]")
        try:
            coords = [float(v) for v in rect]
        except (TypeError, ValueError) as exc:
            raise ValueError(f"{rid}: rect values must be numbers") from exc
        regions.append({"id": rid, "rect": coords})
    return regions


def assign_words(words, regions: list[dict]) -> tuple[list[list], list[str]]:
    """Point-in-rect (bbox center, closed rects, lowest index wins)."""
    buckets: list[list] = [[] for _ in regions]
    errors = []
    for word in words:
        cx, cy = (word[0] + word[2]) / 2, (word[1] + word[3]) / 2
        for index, region in enumerate(regions):
            rect = region["rect"]
            if rect[0] - EPS <= cx <= rect[2] + EPS and rect[1] - EPS <= cy <= rect[3] + EPS:
                buckets[index].append(word)
                break
        else:
            errors.append(f"word outside regions: {word[4]!r} at ({cx:.1f}, {cy:.1f})")
    return buckets, errors


def cmd_plan(args) -> int:
    admitted = admit_or_die(args.page)
    if admitted is not None:
        return admitted
    try:
        regions = load_spec(args.spec)
    except ValueError as exc:
        print(f"error: {exc}")
        return 2

    from render_pdf import render, sha256_of

    pdf_path = Path(args.pdf)
    with pymupdf.open(pdf_path) as document:
        if not 1 <= args.page <= document.page_count:
            print(f"error: page must be 1..{document.page_count}")
            return 2
        page = document[args.page - 1]
        page_rect = page.rect
        words = page.get_text("words")

    errors = geometry_errors(regions, page_rect)
    if errors:
        for message in errors:
            print(message)
        return 1

    # Fresh crop artifacts for this page (old splits are stale; out/ is gitignored).
    for stale in OUT_DIR.glob(f"page-{args.page:03d}-*-region-*.png"):
        stale.unlink(missing_ok=True)
        stale.with_suffix(".json").unlink(missing_ok=True)
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    for index, region in enumerate(regions, 1):
        render(pdf_path, OUT_DIR, args.page, REGION_DPI, tuple(region["rect"]),
               False, label=f"region-{index:02d}")

    buckets, word_errors = assign_words(words, regions)
    if word_errors:
        for message in word_errors:
            print(message)
        return 1

    from fidelity_check import pua_count

    record_id = f"P{args.page:03d}"
    lines = [
        f"id: {record_id}",
        f"page: {args.page}",
        f"source_pdf_sha: {sha256_of(pdf_path)}",
        "status: DRAFT",
        'signed_latex_sha256: ""',
        'signed_on: ""',
        "regions:",
    ]
    for index, (region, assigned) in enumerate(zip(regions, buckets), 1):
        digits = "".join(sorted(
            ch for word in assigned for ch in word_digit_chars(str(word[4]))))
        joined = " ".join(str(word[4]) for word in assigned)
        rect = region["rect"]
        lines += [
            f"  - id: {region['id']}",
            f"    rect: [{rect[0]!r}, {rect[1]!r}, {rect[2]!r}, {rect[3]!r}]",
            f"    crop: page-{args.page:03d}-{REGION_DPI}dpi-region-{index:02d}.png",
            f"    words: {len(assigned)}",
            f'    digits_sorted: "{digits}"',
            f"    pua: {pua_count(joined)}",
            '    notes: ""',
            '    latex: ""',
        ]
    out_path = Path(args.out) if args.out else REGIONS_DIR / f"p{args.page:03d}.yml"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {out_path} ({len(regions)} regions)")
    return 0


def verify_record(path: Path, *, check_freshness: bool = True) -> list[str]:
    """Read-only gates, first failing class wins (all messages of that class).

    check_freshness=False is for signoff: re-approving edited content must
    still pass tiling/latex/digit gates but cannot fail on 'not yet
    re-signed'.
    """
    try:
        record = load_page_record(path)
    except FileNotFoundError as exc:
        return [str(exc)]
    regions = record.get("regions", [])
    if not regions:
        return [f"{path}: no regions listed"]

    rects = []
    for region in regions:
        rect = region.get("rect")
        if not (isinstance(rect, list) and len(rect) == 4):
            return [f"{path}: region {region.get('id', '?')} has no usable rect"]
        rects.append([float(v) for v in rect])
    errors = tiling_errors(rects)
    if errors:
        return errors

    blocks = [r.get("latex", "") for r in regions]
    errors = [f"latex block missing or empty for {r['id']}"
              for r, block in zip(regions, blocks) if not block.strip()]
    if errors:
        return errors

    errors = []
    for region, block in zip(regions, blocks):
        for message in balance_errors(block):
            errors.append(f"{region['id']}: {message}")
    if errors:
        return errors

    # Staleness outranks the digit audit on REVIEWED records: a human
    # signed THIS latex; any edit invalidates the signoff regardless of
    # whether the digits still match.
    if check_freshness and record.get("status") == "REVIEWED":
        stored = record.get("signed_latex_sha256", "")
        current = hashlib.sha256(latex_aggregate(record).encode("utf-8")).hexdigest()
        if not stored or stored != current:
            return [f"stale signoff ({path.name}: latex edited after review)"]

    errors = []
    for region, block in zip(regions, blocks):
        want = str(region.get("digits_sorted", ""))
        got = latex_digits(block)
        if got != want:
            errors.append(f"digit mismatch: {region['id']} latex={got} "
                          f"stored={want} first divergence at {first_divergence(got, want)}")
    want_total, got_total = stored_digits(record), latex_digits(
        "".join(blocks))
    if want_total != got_total:
        errors.append(f"digit mismatch: page total latex={got_total} "
                      f"stored={want_total} first divergence at "
                      f"{first_divergence(got_total, want_total)}")
    return errors


def cmd_verify(args) -> int:
    errors = verify_record(Path(args.record))
    for message in errors:
        print(message)
    return 1 if errors else 0


def cmd_signoff(args) -> int:
    path = Path(args.record)
    # Signoff re-approves the CURRENT content: every gate except freshness
    # must be green (freshness would make re-signing after a review edit
    # impossible). Unreviewed edits are still caught by `verify` and by
    # progress.py until this runs.
    errors = verify_record(path, check_freshness=False)
    if errors:
        for message in errors:
            print(message)
        return 1
    record = load_page_record(path)
    if record.get("status") == "REVIEWED" and record_fresh(record):
        print(f"already REVIEWED and fresh: {path.name}")
        return 0
    aggregate_sha = hashlib.sha256(latex_aggregate(record).encode("utf-8")).hexdigest()
    text = path.read_text(encoding="utf-8")
    text = re.sub(r"(?m)^status: .*$", "status: REVIEWED", text, count=1)
    text = re.sub(r"(?m)^signed_latex_sha256: .*$",
                  f"signed_latex_sha256: {aggregate_sha}", text, count=1)
    text = re.sub(r"(?m)^signed_on: .*$", f"signed_on: {date.today().isoformat()}",
                  text, count=1)
    path.write_text(text, encoding="utf-8")
    print(f"signoff: {path.name} REVIEWED")
    return 0


def cmd_status(args) -> int:
    # Bare integer = page COUNT (the phase switch is `status --pages 33`
    # = pages 1..33); any other spec form is parse_page_spec's page list.
    raw = args.pages.strip()
    pages = list(range(1, int(raw) + 1)) if raw.isdigit() else parse_page_spec(raw)
    ok = True
    for page in pages:
        path = REGIONS_DIR / f"p{page:03d}.yml"
        if not path.is_file():
            print(f"P{page:03d} MISSING")
            ok = False
            continue
        record = load_page_record(path)
        if record.get("status") != "REVIEWED":
            print(f"P{page:03d} {record.get('status', '?')}")
            ok = False
        elif not record_fresh(record):
            print(f"P{page:03d} STALE")
            ok = False
        else:
            print(f"P{page:03d} REVIEWED")
    return 0 if ok else 1


def cmd_export(args) -> int:
    parts = [
        r"\documentclass{article}",
        r"\usepackage{amsmath}",
        r"\usepackage{xcolor}",
        r"\begin{document}",
    ]
    for raw in args.records:
        path = Path(raw)
        record = load_page_record(path)
        parts.append(rf"\section*{{PDF page {record.get('page', '?')}}}")
        for region in record.get("regions", []):
            block = region.get("latex", "")
            if block.strip():
                parts.append(block)
    parts.append(r"\end{document}")
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n\n".join(parts) + "\n", encoding="utf-8")
    print(f"wrote {out_path}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)

    pre = sub.add_parser("precheck", help="stage admission gate (vision probe or fixtures)")
    group = pre.add_mutually_exclusive_group()
    group.add_argument("--check-answer", action="store_true",
                       help="compare out/vision-probe.answer.txt with the probe text")
    group.add_argument("--fixture", action="append", default=[], metavar="PAGE=PATH",
                       help="user-supplied LaTeX fixture for a page (repeatable)")
    pre.add_argument("--pages", default="1-33", metavar="SPEC",
                     help="page scope for --fixture (default 1-33)")

    words = sub.add_parser("words", help="print the page's word boxes for split planning")
    words.add_argument("pdf")
    words.add_argument("page", type=int)

    plan = sub.add_parser("plan", help="validate a split spec, render crops, write record")
    plan.add_argument("pdf")
    plan.add_argument("page", type=int)
    plan.add_argument("--spec", required=True, help="JSON array (literal or file path)")
    plan.add_argument("--out", help="record path (default regions/pNNN.yml)")

    verify = sub.add_parser("verify", help="read-only gates on a record")
    verify.add_argument("record")

    signoff = sub.add_parser(
        "signoff",
        help="mark a verified record REVIEWED (re-signs after review edits)")
    signoff.add_argument("record")

    status = sub.add_parser("status", help="per-page record state (phase-switch gate)")
    status.add_argument("--pages", default="33", metavar="SPEC",
                        help="bare N = pages 1..N (default 33), or a page spec")

    export = sub.add_parser("export", help="one compilable .tex over records")
    export.add_argument("records", nargs="+")
    export.add_argument("--out", required=True)

    args = parser.parse_args(argv)
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")  # Windows cp1252 chokes on symbol words
    handlers = {
        "precheck": cmd_precheck,
        "words": cmd_words,
        "plan": cmd_plan,
        "verify": cmd_verify,
        "signoff": cmd_signoff,
        "status": cmd_status,
        "export": cmd_export,
    }
    try:
        return handlers[args.command](args)
    except (ValueError, FileNotFoundError, FileExistsError) as exc:
        print(f"error: {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
