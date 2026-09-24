"""Stage 1: deterministic PDF extraction with two engines.

Usage:
    python extract.py <pdf> <outdir>

Writes:
    <outdir>/extract_pypdf.txt
    <outdir>/extract_pymupdf.txt
    <outdir>/extract_meta.json   (sha256, pages, per-engine char counts)

Determinism notes: both engines are run fresh each time; outputs are
compared by fidelity_check.py, never trusted alone.
"""
import hashlib
import json
import sys
from pathlib import Path


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def extract_pypdf(pdf: Path) -> list[str]:
    from pypdf import PdfReader

    reader = PdfReader(str(pdf))
    return [(page.extract_text() or "") for page in reader.pages]


def extract_pymupdf(pdf: Path) -> list[str]:
    import pymupdf

    doc = pymupdf.open(str(pdf))
    return [(page.get_text() or "") for page in doc]


def write_transcript(pages: list[str], dest: Path) -> None:
    with dest.open("w", encoding="utf-8", newline="\n") as fh:
        for i, text in enumerate(pages, start=1):
            fh.write(f"=== PAGE {i} ===\n")
            fh.write(text)
            if not text.endswith("\n"):
                fh.write("\n")


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    pdf = Path(sys.argv[1])
    outdir = Path(sys.argv[2])
    if not pdf.is_file():
        print(f"missing pdf: {pdf}")
        return 2
    outdir.mkdir(parents=True, exist_ok=True)

    pypdf_pages = extract_pypdf(pdf)
    mupdf_pages = extract_pymupdf(pdf)

    write_transcript(pypdf_pages, outdir / "extract_pypdf.txt")
    write_transcript(mupdf_pages, outdir / "extract_pymupdf.txt")

    meta = {
        "source_pdf": pdf.name,
        "sha256": sha256_of(pdf),
        "pages": len(pypdf_pages),
        "pypdf_pages": len(pypdf_pages),
        "pymupdf_pages": len(mupdf_pages),
        "pypdf_chars": sum(len(p) for p in pypdf_pages),
        "pymupdf_chars": sum(len(p) for p in mupdf_pages),
    }
    (outdir / "extract_meta.json").write_text(
        json.dumps(meta, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(meta, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
