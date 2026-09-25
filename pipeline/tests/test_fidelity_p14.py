"""Ground-truth-anchored extraction test: page-14 lower half (E/F blocks).

Why this test exists: fidelity_check.py's gate is engine-vs-engine. On
page 14 both engines agree badly in the same way (seq=0.767 MANUAL), so
agreement metrics cannot tell "both wrong identically" from "both right".
This test anchors the E/F region — nested sums, f'(b^n)-g'(h), stacked
fractions over (h-b^n)^2, binomial-coefficient chains, color emphasis —
against a human LaTeX transcription typed from the 300dpi render.

Provenance / regeneration:
    fixture : p14-lower-expected.txt, typed by hand from the render.
              Recreate with:
                python pipeline/01-extract/render_pdf.py PROOF_of_FERMAT.pdf <outdir> --page 14 --dpi 300
              then transcribe the E/F blocks from page-014-300dpi-full.png.
    live    : python pipeline/01-extract/extract.py PROOF_of_FERMAT.pdf <outdir>
              python pipeline/01-extract/fidelity_check.py <outdir>

Fast: milliseconds on the committed fixture + the live page-14 slice.
No Lean, no container, no full re-extract.
"""
import json
import re
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "01-extract"))
import fidelity_check as fc

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "p14-lower-expected.txt"
OUT_DIR = ROOT / "01-extract" / "out"

VAY = "V\u1eady"  # Vậy — anchor where the lower half starts
AP_DUNG = "\u00e1p d\u1ee5ng"  # áp dụng
VI = "v\u00ec"  # vì
PUA_SUM = "\uf0e5"  # what both engines emit for ∑ (U+2211 never appears)
PUA_PRIME = "\uf0a2"  # what both engines emit for ′ (U+2032 never appears)
MINUS = "\u2212"


def read_fixture() -> str:
    if not FIXTURE.is_file():
        raise FileNotFoundError(
            f"missing ground-truth fixture: {FIXTURE}. Recreate it by rendering "
            "python pipeline/01-extract/render_pdf.py PROOF_of_FERMAT.pdf <outdir> "
            "--page 14 --dpi 300 and transcribing the E/F blocks to LaTeX from "
            "page-014-300dpi-full.png (the render is authoritative)."
        )
    return FIXTURE.read_text(encoding="utf-8")


def live_available() -> bool:
    return all(
        (OUT_DIR / name).is_file()
        for name in ("extract_pypdf.txt", "extract_pymupdf.txt", "fidelity_report.json")
    )


LIVE_SKIP = (
    "missing 01-extract/out transcripts/report; regenerate with "
    "python pipeline/01-extract/extract.py PROOF_of_FERMAT.pdf <outdir> && "
    "python pipeline/01-extract/fidelity_check.py <outdir>"
)


def lower_half(page_text: str) -> str:
    """Page-14 text from the Vậy line down (the E/F region)."""
    text = fc.nfc(page_text)
    idx = text.find(fc.nfc(VAY))
    if idx < 0:
        raise AssertionError("lower-half anchor 'Vậy' not found in page-14 text")
    return text[idx:]


def split_ef(lower: str) -> tuple[str, str]:
    """Split the lower half into E-block / F-block at the '*' markers."""
    stars = [m.start() for m in re.finditer(r"\*", lower)]
    if len(stars) != 2:
        raise AssertionError(f"expected 2 '*' block anchors, found {len(stars)}")
    return lower[stars[0] : stars[1]], lower[stars[1] :]


class FidelityUnitTests(unittest.TestCase):
    """Pure-function checks on the v2 gate metrics (no files needed)."""

    def test_seq_ratio_identity(self) -> None:
        self.assertEqual(fc.seq_ratio(["a", "b"], ["a", "b"]), 1.0)

    def test_digit_tripwire_fires_on_single_exponent_flip(self) -> None:
        fixture = read_fixture()
        mutated = fixture.replace("(n-1)", "(n-2)", 1)
        self.assertNotEqual(fixture, mutated)
        self.assertLess(fc.digit_ratio(fixture, mutated), 1.0)


class FixtureGroundTruthTests(unittest.TestCase):
    """The LaTeX fixture itself: structure, coverage, digit inventory."""

    def setUp(self) -> None:
        self.fixture = read_fixture()
        self.lines = self.fixture.splitlines()

    def test_fixture_structure(self) -> None:
        self.assertEqual(len(self.lines), 8)
        self.assertTrue(self.lines[0].startswith("*E"), self.lines[0][:20])
        self.assertEqual(self.lines[4].strip(), "\\\\")
        self.assertTrue(self.lines[5].startswith("* F"), self.lines[5][:20])

    def test_fixture_covers_ef_content(self) -> None:
        e_block = "\n".join(self.lines[0:4])
        f_block = "\n".join(self.lines[5:8])
        self.assertEqual(e_block.count("\\sum"), 2)
        self.assertGreaterEqual(self.fixture.count("\\frac"), 10)
        self.assertIn("f'(b^{n})", e_block)
        self.assertIn("g'(h)", e_block)
        self.assertIn("a^{n(n-1)}", f_block)
        self.assertIn(AP_DUNG, e_block)
        self.assertIn(VI, f_block)

    def test_fixture_digit_inventory(self) -> None:
        self.assertEqual(sorted(set(re.findall(r"\d", self.fixture))),
                         ["0", "1", "2", "3", "4", "5", "6"])


@unittest.skipUnless(live_available(), LIVE_SKIP)
class LivePage14Tests(unittest.TestCase):
    """Page-14 live slice against the report and the fixture."""

    def setUp(self) -> None:
        t1 = (OUT_DIR / "extract_pypdf.txt").read_text(encoding="utf-8")
        t2 = (OUT_DIR / "extract_pymupdf.txt").read_text(encoding="utf-8")
        self.p1 = fc.split_pages(t1)
        self.p2 = fc.split_pages(t2)
        self.assertEqual(len(self.p1), 33)
        self.assertEqual(len(self.p2), 33)
        self.assertIn(VAY, self.p1[13])
        self.assertIn(VAY, self.p2[13])
        self.low1 = lower_half(self.p1[13])
        self.low2 = lower_half(self.p2[13])
        report = json.loads((OUT_DIR / "fidelity_report.json").read_text(encoding="utf-8"))
        entry = [p for p in report["pages"] if p["page"] == 14]
        self.assertEqual(len(entry), 1)
        self.entry = entry[0]

    def test_verdict_locked_manual(self) -> None:
        """p.14 must stay MANUAL: seq in [0.5, 0.8), digits exact, math-dense."""
        self.assertEqual(self.entry["verdict"], "MANUAL")
        self.assertGreaterEqual(self.entry["seq_overlap"], 0.5)
        self.assertLess(self.entry["seq_overlap"], 0.8)
        self.assertEqual(self.entry["digit_overlap"], 1.0)
        self.assertTrue(self.entry["math_dense"])
        self.assertEqual(self.entry["preferred_engine"], "pymupdf")

    def test_symbol_recall_per_engine(self) -> None:
        """Each engine's lower half must carry the E/F content markers."""
        for low in (self.low1, self.low2):
            self.assertIn("abck", low)
            self.assertIn(AP_DUNG, low)
            self.assertIn(VI, low)
            # Both engines emit PUA placeholders for ∑ and ′ — the true
            # symbols never appear, so the text layer cannot be copy-pasted.
            self.assertIn(PUA_SUM, low)
            self.assertIn(PUA_PRIME, low)
            stripped = re.sub(r"\s+", "", low)
            self.assertIn("(h", stripped)
        # Tokenization differs per engine: pypdf glues labels (nE/nF),
        # pymupdf keeps standalone E/F tokens.
        toks1, toks2 = self.low1.split(), self.low2.split()
        self.assertIn("nE", toks1)
        self.assertIn("nF", toks1)
        self.assertIn("E", toks2)
        self.assertIn("F", toks2)
        # F-block carries the abck chains in both engines.
        _, f1 = split_ef(self.low1)
        _, f2 = split_ef(self.low2)
        self.assertGreaterEqual(sum(1 for t in f1.split() if "abck" in t), 10)
        self.assertGreaterEqual(sum(1 for t in f2.split() if "abck" in t), 10)
        # Structural agreement: paren/equation/minus counts match exactly.
        for count in (
            lambda s: s.count("("),
            lambda s: s.count(")"),
            lambda s: s.count("="),
            lambda s: s.count(MINUS),
        ):
            self.assertEqual(count(self.low1), count(self.low2))
        self.assertGreater(self.low1.count("("), 50)

    def test_actionables_point_at_ef(self) -> None:
        """The non-OK entry must give spans, not just a number."""
        diff = self.entry.get("diff", {})
        self.assertTrue(diff.get("first_pypdf"))
        self.assertTrue(diff.get("first_pymupdf"))
        uniq_p = [t for t, _ in self.entry.get("unique_pypdf", [])]
        uniq_m = [t for t, _ in self.entry.get("unique_pymupdf", [])]
        self.assertTrue(uniq_p)
        self.assertTrue(uniq_m)
        # pypdf leaks degenerate equation fragments; pymupdf keeps the
        # standalone E label pypdf glued onto nE.
        self.assertIn("nn", uniq_p)
        self.assertIn("E", uniq_m)

    def test_blocks_math_dense_and_readable(self) -> None:
        """E/F blocks route math-dense; readability prefers pymupdf on F."""
        e1, f1 = split_ef(self.low1)
        e2, f2 = split_ef(self.low2)
        for block in (e1, f1, e2, f2):
            self.assertGreater(fc.math_density(block), fc.DENSITY_THRESHOLD)
        r1, r2 = fc.readability(f1), fc.readability(f2)
        self.assertLess(
            (r2["degenerate"], -r2["words"]), (r1["degenerate"], -r1["words"])
        )

    def test_fixture_digits_covered_by_live(self) -> None:
        """Every digit class in the ground truth must appear in both engines."""
        expected = set(re.findall(r"\d", read_fixture()))
        for low in (self.low1, self.low2):
            self.assertLessEqual(expected, set(re.findall(r"\d", low)))


if __name__ == "__main__":
    unittest.main()
