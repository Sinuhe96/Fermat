import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import pymupdf


ROOT = Path(__file__).resolve().parents[1]
RENDERER = ROOT / "01-extract" / "render_pdf.py"


class RenderPdfTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        self.pdf = self.root / "fixture.pdf"
        document = pymupdf.open()
        page = document.new_page(width=200, height=100)
        page.insert_text((20, 30), "deterministic fixture")
        document.save(self.pdf)
        document.close()

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def run_renderer(self, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(RENDERER), str(self.pdf), str(self.root / "out"), *arguments],
            capture_output=True,
            text=True,
        )

    def test_full_page_is_repeatable_and_records_hashes(self) -> None:
        first = self.run_renderer("--page", "1", "--dpi", "72")
        self.assertEqual(first.returncode, 0, first.stderr)
        image = self.root / "out" / "page-001-72dpi-full.png"
        metadata_path = image.with_suffix(".json")
        first_image = image.read_bytes()
        first_metadata = metadata_path.read_bytes()

        second = self.run_renderer("--page", "1", "--dpi", "72")
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertEqual(image.read_bytes(), first_image)
        self.assertEqual(metadata_path.read_bytes(), first_metadata)

        metadata = json.loads(first_metadata)
        self.assertEqual(metadata["source_file"], "fixture.pdf")
        self.assertEqual(metadata["source_sha256"], hashlib.sha256(self.pdf.read_bytes()).hexdigest())
        self.assertEqual(metadata["output_sha256"], hashlib.sha256(first_image).hexdigest())
        self.assertNotIn("timestamp", metadata)
        pixmap = pymupdf.Pixmap(image)
        self.assertEqual((pixmap.width, pixmap.height), (200, 100))

    def test_crop_has_expected_dimensions(self) -> None:
        result = self.run_renderer(
            "--page", "1", "--dpi", "72", "--crop", "10,20,110,70"
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        image = self.root / "out" / "page-001-72dpi-crop-10-20-110-70.png"
        pixmap = pymupdf.Pixmap(image)
        self.assertEqual((pixmap.width, pixmap.height), (100, 50))
        metadata = json.loads(image.with_suffix(".json").read_text(encoding="utf-8"))
        self.assertEqual(metadata["requested_crop_points"], [10.0, 20.0, 110.0, 70.0])

    def test_invalid_arguments_fail(self) -> None:
        cases = (
            ("--page", "0"),
            ("--page", "2"),
            ("--page", "1", "--dpi", "0"),
            ("--page", "1", "--crop", "0,0,300,50"),
            ("--page", "1", "--crop", "0,0,0,50"),
        )
        for arguments in cases:
            with self.subTest(arguments=arguments):
                self.assertNotEqual(self.run_renderer(*arguments).returncode, 0)

    def test_differing_artifact_requires_force(self) -> None:
        result = self.run_renderer("--page", "1", "--dpi", "72")
        self.assertEqual(result.returncode, 0, result.stderr)
        image = self.root / "out" / "page-001-72dpi-full.png"
        image.write_bytes(b"different")
        self.assertNotEqual(self.run_renderer("--page", "1", "--dpi", "72").returncode, 0)
        forced = self.run_renderer("--page", "1", "--dpi", "72", "--force")
        self.assertEqual(forced.returncode, 0, forced.stderr)
        self.assertNotEqual(image.read_bytes(), b"different")


if __name__ == "__main__":
    unittest.main()
