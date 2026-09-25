"""Gate tests for the vision->LaTeX region extraction tool (01-extract/regions.py).

Covers, per the pipeline plan:
  - stage admission: vision probe (bare render -> answer check -> pass file)
    and user-supplied LaTeX fixtures; `plan` refuses without admission;
  - plan-time geometry gates: exact tiling, disjointness, coverage sweep,
    region count/size/page containment, deterministic word assignment;
  - verify-time gates: latex presence, balance, digit audit (comments,
    \\label, exponent digits), signoff staleness;
  - signoff/status/export mechanics.

All state is redirected to a temp dir (regions.OUT_DIR / REGIONS_DIR /
PASS_FILE are patched); the fixture PDF is synthetic (2 pages, 400x300pt).
No repo files are touched, no Lean, no container.
"""
import contextlib
import hashlib
import io
import json
import sys
import tempfile
import unittest
from datetime import date
from pathlib import Path

import pymupdf

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "01-extract"))
import regions

PROBE_ANSWER = "\\[ f′(b^{2}) = 73 + h^{n-1} \\]\n"  # wrapped + prime variant
SPEC_2BAND = json.dumps([
    {"id": "R1", "rect": [0, 0, 400, 150]},
    {"id": "R2", "rect": [0, 150, 400, 300]},
])


def make_pdf(path: Path) -> None:
    document = pymupdf.open()
    for index in range(2):
        page = document.new_page(width=400, height=300)
        if index == 0:
            page.insert_text((20, 30), "a2")    # band 1 (center y ~28)
            page.insert_text((20, 200), "b3")   # band 2 (center y ~196)
    document.save(path)
    document.close()


class RegionsTestCase(unittest.TestCase):
    """Base: temp dirs, patched module state, fixture PDF, CLI runner."""

    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        self.pdf = self.root / "fixture.pdf"
        make_pdf(self.pdf)
        self.out = self.root / "out"
        self.reg = self.root / "regions"
        self.reg.mkdir()
        self._saved = (regions.OUT_DIR, regions.REGIONS_DIR, regions.PASS_FILE)
        regions.OUT_DIR = self.out
        regions.REGIONS_DIR = self.reg
        regions.PASS_FILE = self.out / "vision-probe.pass"

    def tearDown(self) -> None:
        regions.OUT_DIR, regions.REGIONS_DIR, regions.PASS_FILE = self._saved
        self.tempdir.cleanup()

    def run_cli(self, *argv: str) -> tuple[int, str]:
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            code = regions.main(list(argv))
        return code, buffer.getvalue()

    def admit_probe(self) -> None:
        code, text = self.run_cli("precheck")
        self.assertEqual(code, 2, text)
        (self.out / "vision-probe.answer.txt").write_text(
            PROBE_ANSWER, encoding="utf-8")
        code, text = self.run_cli("precheck", "--check-answer")
        self.assertEqual(code, 0, text)

    def plan(self, spec: str, page: int = 1) -> tuple[int, str]:
        return self.run_cli("plan", str(self.pdf), str(page), "--spec", spec)

    def write_record(self, latex: str, digits: str, status: str = "DRAFT",
                     signed: str = "", page: int = 3, regions_yaml: str = "") -> Path:
        """Hand-built record for verify/signoff/status/export tests."""
        body = "\n".join("      " + line for line in latex.splitlines())
        content = (
            f"id: P{page:03d}\n"
            f"page: {page}\n"
            "source_pdf_sha: deadbeef\n"
            f"status: {status}\n"
            f"signed_latex_sha256: {signed}\n"
            "signed_on: \n"
            "regions:\n"
        )
        if regions_yaml:
            content += regions_yaml
        else:
            content += (
                "  - id: R1\n"
                "    rect: [0.0, 0.0, 400.0, 300.0]\n"
                f"    crop: page-{page:03d}-300dpi-region-01.png\n"
                "    words: 2\n"
                f'    digits_sorted: "{digits}"\n'
                "    pua: 0\n"
                '    notes: ""\n'
                "    latex: |\n"
                f"{body}\n"
            )
        path = self.reg / f"p{page:03d}.yml"
        path.write_text(content, encoding="utf-8")
        return path


class PrecheckTests(RegionsTestCase):
    def test_bare_precheck_renders_probe_and_awaits(self) -> None:
        code, text = self.run_cli("precheck")
        self.assertEqual(code, 2)
        self.assertIn("awaiting vision answer", text)
        self.assertTrue((self.out / "vision-probe.png").is_file())
        expected = (self.out / "vision-probe.expected.txt").read_text(encoding="utf-8")
        self.assertEqual(expected.strip(), regions.PROBE_TEXT)

    def test_check_answer_without_file_fails(self) -> None:
        self.run_cli("precheck")  # renders probe, writes expected
        code, text = self.run_cli("precheck", "--check-answer")
        self.assertEqual(code, 1)
        self.assertIn("answer file missing: out/vision-probe.answer.txt", text)

    def test_wrapped_variant_answer_passes(self) -> None:
        self.run_cli("precheck")
        (self.out / "vision-probe.answer.txt").write_text(
            PROBE_ANSWER, encoding="utf-8")
        code, text = self.run_cli("precheck", "--check-answer")
        self.assertEqual(code, 0, text)
        self.assertIn("vision probe passed", text)
        state = (self.out / "vision-probe.pass").read_text(encoding="utf-8")
        self.assertIn("mode=probe", state)
        self.assertIn(f"expected_sha256={regions.probe_sha()}", state)

    def test_single_digit_flip_fails_probe(self) -> None:
        self.run_cli("precheck")
        (self.out / "vision-probe.answer.txt").write_text(
            PROBE_ANSWER.replace("73", "74"), encoding="utf-8")
        code, text = self.run_cli("precheck", "--check-answer")
        self.assertEqual(code, 1)
        self.assertIn("vision probe mismatch", text)

    def test_fixture_admission_requires_every_page(self) -> None:
        f3 = self.root / "p3.tex"
        f7 = self.root / "p7.tex"
        for path in (f3, f7):
            path.write_text("\\[ a^{12} \\]\n", encoding="utf-8")
        code, text = self.run_cli(
            "precheck", "--fixture", f"3={f3}", "--pages", "3,7")
        self.assertEqual(code, 1)
        self.assertIn("vision model required: pages 7 lack fixtures", text)
        code, text = self.run_cli(
            "precheck", "--fixture", f"3={f3}", "--fixture", f"7={f7}",
            "--pages", "3,7")
        self.assertEqual(code, 0, text)
        self.assertIn("fixture-admitted: pages 3,7", text)
        state = (self.out / "vision-probe.pass").read_text(encoding="utf-8")
        self.assertIn("mode=fixtures", state)
        self.assertIn("pages=3,7", state)


class AdmissionTests(RegionsTestCase):
    def test_plan_without_pass_file_refused(self) -> None:
        code, text = self.plan(SPEC_2BAND)
        self.assertEqual(code, 1)
        self.assertIn("precheck not passed (run regions.py precheck)", text)
        self.assertFalse((self.reg / "p001.yml").exists())

    def test_probe_pass_admits_any_page_but_gates_still_judge(self) -> None:
        self.admit_probe()
        code, text = self.plan(SPEC_2BAND)
        self.assertEqual(code, 0, text)
        gap = json.dumps([
            {"id": "R1", "rect": [0, 0, 400, 150]},
            {"id": "R2", "rect": [0, 200, 400, 300]},
        ])
        code, text = self.plan(gap)
        self.assertEqual(code, 1)
        self.assertIn("uncovered cell", text)

    def test_fixture_pass_admits_only_listed_pages(self) -> None:
        f1 = self.root / "p1.tex"
        f1.write_text("\\[ a^{12} \\]\n", encoding="utf-8")
        code, text = self.run_cli("precheck", "--fixture", f"1={f1}", "--pages", "1")
        self.assertEqual(code, 0, text)
        code, text = self.plan(SPEC_2BAND, page=2)  # page 2 not listed
        self.assertEqual(code, 1)
        self.assertIn("precheck not passed", text)
        f2 = self.root / "p2.tex"
        f2.write_text("\\[ b^{34} \\]\n", encoding="utf-8")
        code, text = self.run_cli(
            "precheck", "--fixture", f"1={f1}", "--fixture", f"2={f2}",
            "--pages", "1,2")
        self.assertEqual(code, 0, text)
        code, text = self.plan(SPEC_2BAND, page=2)  # blank page 2: 0 words
        self.assertEqual(code, 0, text)


class TilingTests(RegionsTestCase):
    def setUp(self) -> None:
        super().setUp()
        self.admit_probe()

    def test_exact_tiling_accepted_and_record_written(self) -> None:
        code, text = self.plan(SPEC_2BAND)
        self.assertEqual(code, 0, text)
        record = regions.load_page_record(self.reg / "p001.yml")
        self.assertEqual(record["id"], "P001")
        self.assertEqual(record["status"], "DRAFT")
        self.assertEqual(len(record["regions"]), 2)
        first, second = record["regions"]
        self.assertEqual(first["rect"], [0.0, 0.0, 400.0, 150.0])
        self.assertEqual(int(first["words"]), 1)
        self.assertEqual(first["digits_sorted"], "2")
        self.assertEqual(int(second["words"]), 1)
        self.assertEqual(second["digits_sorted"], "3")
        self.assertEqual(int(first["pua"]), 0)
        self.assertTrue((self.out / "page-001-300dpi-region-01.png").is_file())
        self.assertTrue((self.out / "page-001-300dpi-region-01.json").is_file())
        self.assertTrue((self.out / "page-001-300dpi-region-02.png").is_file())

    def test_gap_names_uncovered_cell(self) -> None:
        spec = json.dumps([
            {"id": "R1", "rect": [0, 0, 400, 150]},
            {"id": "R2", "rect": [0, 200, 400, 300]},
        ])
        code, text = self.plan(spec)
        self.assertEqual(code, 1)
        self.assertIn("uncovered cell [0.0, 150.0, 400.0, 200.0]", text)

    def test_interior_overlap_names_pair(self) -> None:
        spec = json.dumps([
            {"id": "R1", "rect": [0, 0, 400, 200]},
            {"id": "R2", "rect": [0, 150, 400, 300]},
        ])
        code, text = self.plan(spec)
        self.assertEqual(code, 1)
        self.assertIn("R1 overlaps R2", text)

    def test_out_of_page_rect_named(self) -> None:
        code, text = self.plan(json.dumps([{"id": "R1", "rect": [-10, 0, 400, 300]}]))
        self.assertEqual(code, 1)
        self.assertIn("outside page", text)

    def test_region_count_and_size_rejected(self) -> None:
        thirteen = json.dumps(
            [{"id": f"R{i}", "rect": [0, 0, 400, 300]} for i in range(1, 14)])
        code, text = self.plan(thirteen)
        self.assertEqual(code, 1)
        self.assertIn("region count 13 outside 1-12", text)
        short = json.dumps([
            {"id": "R1", "rect": [0, 0, 400, 50]},
            {"id": "R2", "rect": [0, 50, 400, 300]},
        ])
        code, text = self.plan(short)
        self.assertEqual(code, 1)
        self.assertIn("height 50.0pt < 60pt", text)

    def test_word_assignment_boundary_and_outside(self) -> None:
        spec = [
            {"id": "R1", "rect": [0.0, 0.0, 400.0, 150.0]},
            {"id": "R2", "rect": [0.0, 150.0, 400.0, 300.0]},
        ]
        words = [
            (100.0, 148.0, 140.0, 152.0, "bd", 0, 0, 0),  # center y = 150.0
            (500.0, 50.0, 540.0, 60.0, "out", 0, 0, 0),
        ]
        buckets, errors = regions.assign_words(words, spec)
        # boundary word goes to the lowest-index region (closed rects)
        self.assertEqual([w[4] for w in buckets[0]], ["bd"])
        self.assertEqual(buckets[1], [])
        self.assertEqual(len(errors), 1)
        self.assertIn("word outside regions", errors[0])
        self.assertIn("'out'", errors[0])


class VerifyTests(RegionsTestCase):
    def test_correct_latex_exit_zero(self) -> None:
        path = self.write_record("\\[ a^{12} \\]", "12")
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 0, text)

    def test_digit_flip_names_region_and_divergence(self) -> None:
        path = self.write_record("\\[ a^{13} \\]", "12")
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 1)
        self.assertIn("digit mismatch: R1", text)
        self.assertIn("first divergence at", text)

    def test_duplicated_digits_fail_audit(self) -> None:
        path = self.write_record("\\[ a^{12} b^{12} \\]", "12")
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 1)
        self.assertIn("digit mismatch", text)

    def test_comment_and_label_digits_ignored(self) -> None:
        path = self.write_record("\\[%99 comment\n a^{12} \\label{eq2}\\]", "12")
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 0, text)

    def test_exponent_digits_counted(self) -> None:
        path = self.write_record("\\[ 2^{10} \\]", "012")
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 0, text)

    def test_unbalanced_delimiters_fail(self) -> None:
        path = self.write_record("\\[ a^{12} ", "12")
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 1)
        self.assertIn("unpaired", text)

    def test_missing_latex_block_fails(self) -> None:
        path = self.write_record("   ", "12")
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 1)
        self.assertIn("latex block missing or empty for R1", text)

    def test_signoff_then_edit_is_stale(self) -> None:
        path = self.write_record("\\[ a^{12} \\]", "12")
        code, text = self.run_cli("signoff", str(path))
        self.assertEqual(code, 0, text)
        signed = path.read_text(encoding="utf-8")
        self.assertIn("status: REVIEWED", signed)
        expected_sha = hashlib.sha256("\\[ a^{12} \\]".encode("utf-8")).hexdigest()
        self.assertIn(f"signed_latex_sha256: {expected_sha}", signed)
        self.assertIn(f"signed_on: {date.today().isoformat()}", signed)
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 0, text)
        # letter edit keeps digits identical: only staleness can catch it
        path.write_text(signed.replace("\\[ a^{12} \\]", "\\[ c^{12} \\]"),
                        encoding="utf-8")
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 1)
        self.assertIn("stale signoff", text)
        # review edit -> signoff re-adopts the current content (all other
        # gates re-checked) and the record is fresh again
        code, text = self.run_cli("signoff", str(path))
        self.assertEqual(code, 0, text)
        code, text = self.run_cli("verify", str(path))
        self.assertEqual(code, 0, text)
        resigned = path.read_text(encoding="utf-8")
        self.assertIn(
            f"signed_latex_sha256: "
            f"{hashlib.sha256('\\[ c^{12} \\]'.encode('utf-8')).hexdigest()}",
            resigned)
        # a digit flip still blocks re-signoff (digits gate stays active)
        path.write_text(resigned.replace("c^{12}", "c^{13}"), encoding="utf-8")
        code, text = self.run_cli("signoff", str(path))
        self.assertEqual(code, 1)
        self.assertIn("digit mismatch", text)

    def test_status_reports_all_states(self) -> None:
        code, text = self.run_cli("status", "--pages", "3-3")
        self.assertEqual(code, 1)
        self.assertIn("P003 MISSING", text)
        path = self.write_record("\\[ a^{12} \\]", "12")
        code, text = self.run_cli("status", "--pages", "3-3")
        self.assertEqual(code, 1)
        self.assertIn("P003 DRAFT", text)
        code, text = self.run_cli("signoff", str(path))
        self.assertEqual(code, 0, text)
        code, text = self.run_cli("status", "--pages", "3-3")
        self.assertEqual(code, 0, text)
        self.assertIn("P003 REVIEWED", text)
        signed = path.read_text(encoding="utf-8")
        path.write_text(signed.replace("a^{12}", "a^{13}"), encoding="utf-8")
        code, text = self.run_cli("status", "--pages", "3-3")
        self.assertEqual(code, 1)
        self.assertIn("P003 STALE", text)

    def test_export_writes_compilable_document(self) -> None:
        regions_yaml = (
            "  - id: R1\n"
            "    rect: [0.0, 0.0, 400.0, 150.0]\n"
            "    crop: c1.png\n"
            "    words: 1\n"
            '    digits_sorted: "1"\n'
            "    pua: 0\n"
            '    notes: ""\n'
            "    latex: |\n"
            "      \\[ A^{1} \\]\n"
            "  - id: R2\n"
            "    rect: [0.0, 150.0, 400.0, 300.0]\n"
            "    crop: c2.png\n"
            "    words: 1\n"
            '    digits_sorted: "2"\n'
            "    pua: 0\n"
            '    notes: ""\n'
            "    latex: |\n"
            "      \\[ B^{2} \\]\n"
        )
        path = self.write_record("", "", regions_yaml=regions_yaml)
        out = self.root / "review.tex"
        code, text = self.run_cli("export", str(path), "--out", str(out))
        self.assertEqual(code, 0, text)
        document = out.read_text(encoding="utf-8")
        self.assertIn(r"\documentclass{article}", document)
        self.assertIn(r"\begin{document}", document)
        self.assertIn(r"\section*{PDF page 3}", document)
        self.assertIn("\\[ A^{1} \\]", document)
        self.assertIn("\\[ B^{2} \\]", document)
        self.assertIn(r"\end{document}", document)


class RecordParserTests(RegionsTestCase):
    def test_pua_encoded_superscript_digits_counted(self) -> None:
        # Field finding: symbol-font superscript digit k arrives in the
        # text layer as U+F030+k, not as ASCII — the audit must see it.
        self.assertEqual(regions.word_digit_chars("a\uf034b\uf033c"), ["4", "3"])
        self.assertEqual(regions.word_digit_chars("n2\uf032"), ["2", "2"])
        self.assertEqual(regions.word_digit_chars("\uf0e5 \uf0a2"), [])  # ∑/′ PUA stay non-digits

    def test_load_page_record_roundtrip(self) -> None:
        path = self.write_record("\\[ a^{12} \\]", "12",
                                 regions_yaml=(
                                     "  - id: R1\n"
                                     "    rect: [1.5, 2.5, 300.0, 400.0]\n"
                                     "    crop: c1.png\n"
                                     "    words: 7\n"
                                     '    digits_sorted: "12"\n'
                                     "    pua: 3\n"
                                     '    notes: "prime ambiguous"\n'
                                     "    latex: |\n"
                                     "      \\[ a^{12} \\]\n"
                                     "      more \\[ b^{3} \\]\n"))
        record = regions.load_page_record(path)
        self.assertEqual(record["page"], "3")
        self.assertEqual(record["regions"][0]["rect"], [1.5, 2.5, 300.0, 400.0])
        self.assertEqual(record["regions"][0]["notes"], "prime ambiguous")
        self.assertEqual(record["regions"][0]["latex"],
                         "\\[ a^{12} \\]\nmore \\[ b^{3} \\]")
        self.assertEqual(regions.latex_aggregate(record),
                         record["regions"][0]["latex"])


if __name__ == "__main__":
    unittest.main()
