"""Stage 1: deterministic PDF extraction with two engines.

Usage:
    python extract.py <pdf> <outdir> [--pages PAGE [PAGE ...]]

Writes:
    <outdir>/extract_pypdf.txt
    <outdir>/extract_pymupdf.txt
    <outdir>/extract_meta.json   (sha256, pages, per-engine char counts)

Both engines run fresh each time. Full extraction is the default; --pages is
for fast readiness checks and retains the original one-based page labels.
"""

import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_pages(selected: list[int] | None, page_count: int) -> list[int]:
    pages = selected if selected is not None else list(range(1, page_count + 1))
    if not pages:
        raise ValueError("at least one page is required")
    if len(set(pages)) != len(pages):
        raise ValueError("page numbers must be unique")
    if any(page < 1 or page > page_count for page in pages):
        raise ValueError(f"pages must be between 1 and {page_count}")
    return pages


def extract_pypdf(pdf: Path, selected: list[int] | None) -> tuple[int, list[int], list[str]]:
    from pypdf import PdfReader

    reader = PdfReader(str(pdf))
    pages = validate_pages(selected, len(reader.pages))
    return len(reader.pages), pages, [(reader.pages[page - 1].extract_text() or "") for page in pages]


def extract_pymupdf(pdf: Path, pages: list[int]) -> tuple[int, list[str]]:
    import pymupdf

    with pymupdf.open(pdf) as document:
        if document.page_count < max(pages):
            raise ValueError("PDF engines disagree on page count")
        return document.page_count, [(document[page - 1].get_text() or "") for page in pages]


def write_transcript(page_numbers: list[int], texts: list[str], dest: Path) -> None:
    with dest.open("w", encoding="utf-8", newline="\n") as handle:
        for page, text in zip(page_numbers, texts, strict=True):
            handle.write(f"=== PAGE {page} ===\n")
            handle.write(text)
            if not text.endswith("\n"):
                handle.write("\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pdf", type=Path)
    parser.add_argument("outdir", type=Path)
    parser.add_argument("--pages", type=int, nargs="+")
    args = parser.parse_args()

    if not args.pdf.is_file():
        parser.error(f"missing PDF: {args.pdf}")
    args.outdir.mkdir(parents=True, exist_ok=True)

    try:
        page_count, pages, pypdf_pages = extract_pypdf(args.pdf, args.pages)
        mupdf_page_count, mupdf_pages = extract_pymupdf(args.pdf, pages)
    except ValueError as exc:
        parser.error(str(exc))
    if page_count != mupdf_page_count:
        parser.error(f"PDF engines disagree on page count: {page_count} != {mupdf_page_count}")

    write_transcript(pages, pypdf_pages, args.outdir / "extract_pypdf.txt")
    write_transcript(pages, mupdf_pages, args.outdir / "extract_pymupdf.txt")

    metadata = {
        "source_pdf": args.pdf.name,
        "sha256": sha256_of(args.pdf),
        "pages": page_count,
        "selected_pages": pages,
        "pypdf_pages": len(pypdf_pages),
        "pymupdf_pages": len(mupdf_pages),
        "pypdf_chars": sum(len(page) for page in pypdf_pages),
        "pymupdf_chars": sum(len(page) for page in mupdf_pages),
        "pypdf_version": importlib.metadata.version("pypdf"),
        "pymupdf_version": importlib.metadata.version("PyMuPDF"),
    }
    (args.outdir / "extract_meta.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(metadata, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
