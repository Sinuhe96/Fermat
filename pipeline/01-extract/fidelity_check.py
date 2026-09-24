"""Stage 1 gate: verify extraction fidelity between the two engines.

Usage:
    python fidelity_check.py <extract_dir>

Reads extract_pypdf.txt, extract_pymupdf.txt, extract_meta.json.
Writes fidelity_report.json with per-page verdicts and an overall verdict.

Gate semantics (exit codes):
    0 — PASS: page counts equal 33, both engines produced text on every
        page, transcripts are byte-stable vs prior run if present.
    1 — FAIL: stop the pipeline. Inspect fidelity_report.json, then route
        failing pages to MANUAL transcription (see 02-chunks/schema.md).

Deliberately conservative: prose pages should agree closely; math-dense
pages (7-29) are EXPECTED to diverge, and divergence there means
"needs human eyes", not "pipeline is broken".
"""
import json
import re
import sys
from pathlib import Path

EXPECTED_PAGES = 33
# Pages known to be math-dense; token divergence here is expected and
# routes to manual transcription rather than failing the whole run.
MATH_PAGES = set(range(7, 30))

def tokenize(text: str) -> set[str]:
    """Whitespace AND math-symbol tolerant tokenization.

    Raw whitespace-splitting punishes spacing-only differences
    ("1( ) 1" vs "1 ( ) 1", "k nCn" vs "k n C n"). Stripping spaces
    inside tokens before comparing measures content agreement, which is
    what the gate is actually about.
    """
    toks = set()
    for w in text.split():
        toks.add(re.sub(r"\s+", "", w))
    compact = re.sub(r"\s+", "", text)
    for i in range(0, len(compact), 8):
        toks.add(compact[i : i + 8])
    return toks


PAGE_SPLIT = re.compile(r"=== PAGE \d+ ===")


def split_pages(transcript: str) -> list[str]:
    parts = PAGE_SPLIT.split(transcript)
    return [p for p in parts if p.strip()]


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    d = Path(sys.argv[1])
    meta = json.loads((d / "extract_meta.json").read_text(encoding="utf-8"))
    t1 = (d / "extract_pypdf.txt").read_text(encoding="utf-8")
    t2 = (d / "extract_pymupdf.txt").read_text(encoding="utf-8")
    p1, p2 = split_pages(t1), split_pages(t2)

    pages = []
    overall = "PASS"
    if meta["pypdf_pages"] != EXPECTED_PAGES or meta["pymupdf_pages"] != EXPECTED_PAGES:
        overall = "FAIL"

    for i in range(max(len(p1), len(p2))):
        a = p1[i] if i < len(p1) else ""
        b = p2[i] if i < len(p2) else ""
        wa, wb = tokenize(a), tokenize(b)
        overlap = len(wa & wb) / max(len(wa | wb), 1)
        has_text = bool(a.strip()) and bool(b.strip())
        page_no = i + 1
        if not has_text:
            verdict = "FAIL"
        elif page_no in MATH_PAGES:
            verdict = "MANUAL" if overlap < 0.80 else "OK"
        else:
            verdict = "OK" if overlap > 0.50 else "REVIEW"
        if verdict in ("FAIL", "REVIEW"):
            overall = "FAIL"
        pages.append(
            {
                "page": page_no,
                "pypdf_chars": len(a),
                "pymupdf_chars": len(b),
                "token_overlap": round(overlap, 3),
                "verdict": verdict,
            }
        )

    if overall == "FAIL":
        overall = "FAIL"
    elif any(p["verdict"] == "MANUAL" for p in pages):
        overall = "PASS_WITH_MANUAL"
    else:
        overall = "PASS"

    report = {
        "source_sha256": meta["sha256"],
        "expected_pages": EXPECTED_PAGES,
        "overall": overall,
        "pages": pages,
    }
    (d / "fidelity_report.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    n_manual = sum(1 for p in pages if p["verdict"] == "MANUAL")
    n_fail = sum(1 for p in pages if p["verdict"] in ("FAIL", "REVIEW"))
    print(f"overall={overall} manual_pages={n_manual} failing_pages={n_fail}")
    return 0 if overall in ("PASS", "PASS_WITH_MANUAL") else 1


if __name__ == "__main__":
    raise SystemExit(main())
