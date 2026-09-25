"""Stage 1 gate: verify extraction fidelity between the two engines.

Usage:
    python fidelity_check.py <extract_dir>

Reads extract_pypdf.txt, extract_pymupdf.txt, extract_meta.json.
Writes fidelity_report.json with per-page verdicts and an overall verdict.

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
import json
import re
import sys
import unicodedata
from collections import Counter
from pathlib import Path

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
    return 0 if overall in ("PASS", "PASS_WITH_MANUAL") else 1


if __name__ == "__main__":
    raise SystemExit(main())
