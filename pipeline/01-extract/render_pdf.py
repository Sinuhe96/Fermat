"""Render a PDF page or crop to a provenance-recorded PNG."""

import argparse
import hashlib
import json
import re
from pathlib import Path

import pymupdf


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized_number(value: float) -> str:
    text = f"{value:.6f}".rstrip("0").rstrip(".")
    return text.replace("-", "m").replace(".", "p")


def parse_crop(value: str) -> tuple[float, float, float, float]:
    try:
        parts = tuple(float(part.strip()) for part in value.split(","))
    except ValueError as exc:
        raise argparse.ArgumentTypeError("crop must contain four numbers") from exc
    if len(parts) != 4:
        raise argparse.ArgumentTypeError("crop must be x0,y0,x1,y1")
    return parts


def rect_values(rect: pymupdf.Rect) -> list[float]:
    return [round(value, 6) for value in (rect.x0, rect.y0, rect.x1, rect.y1)]


def artifact_name(page: int, dpi: int, crop: tuple[float, float, float, float] | None,
                  label: str | None = None) -> str:
    if label is not None:
        if not re.fullmatch(r"[A-Za-z0-9._-]+", label):
            raise ValueError(f"invalid artifact label: {label!r}")
        suffix = label
    elif crop is not None:
        suffix = "crop-" + "-".join(normalized_number(value) for value in crop)
    else:
        suffix = "full"
    return f"page-{page:03d}-{dpi}dpi-{suffix}.png"


def write_artifacts(image_path: Path, image: bytes, metadata: bytes, force: bool) -> None:
    metadata_path = image_path.with_suffix(".json")
    for path, content in ((image_path, image), (metadata_path, metadata)):
        if path.exists() and path.read_bytes() != content and not force:
            raise FileExistsError(f"refusing to replace differing artifact: {path}")
    image_path.write_bytes(image)
    metadata_path.write_bytes(metadata)


def render(pdf: Path, outdir: Path, page_number: int, dpi: int,
           crop: tuple[float, float, float, float] | None, force: bool,
           label: str | None = None) -> tuple[Path, Path]:
    if not pdf.is_file():
        raise FileNotFoundError(f"missing PDF: {pdf}")
    if dpi <= 0:
        raise ValueError("DPI must be positive")

    with pymupdf.open(pdf) as document:
        if not 1 <= page_number <= document.page_count:
            raise ValueError(f"page must be between 1 and {document.page_count}")
        page = document[page_number - 1]
        page_rect = page.rect
        clip = page_rect
        if crop is not None:
            clip = pymupdf.Rect(crop)
            if (clip.is_empty or clip.is_infinite or clip.x0 < page_rect.x0
                    or clip.y0 < page_rect.y0 or clip.x1 > page_rect.x1
                    or clip.y1 > page_rect.y1):
                raise ValueError(f"crop must be a non-empty rectangle inside {rect_values(page_rect)}")

        scale = dpi / 72
        matrix = pymupdf.Matrix(scale, scale)
        pixmap = page.get_pixmap(
            matrix=matrix,
            colorspace=pymupdf.csRGB,
            alpha=False,
            annots=False,
            clip=clip,
        )
        image = pixmap.tobytes("png")
        page_count = document.page_count

    outdir.mkdir(parents=True, exist_ok=True)
    image_path = outdir / artifact_name(page_number, dpi, crop, label)
    metadata_record = {
        "dpi": dpi,
        "effective_crop_points": rect_values(clip),
        "matrix": [round(scale, 8), round(scale, 8)],
        "output_file": image_path.name,
        "output_sha256": hashlib.sha256(image).hexdigest(),
        "page": page_number,
        "page_count": page_count,
        "page_rect_points": rect_values(page_rect),
        "pymupdf_version": pymupdf.__version__,
        "requested_crop_points": list(crop) if crop is not None else None,
        "source_file": pdf.name,
        "source_sha256": sha256_of(pdf),
    }
    if label is not None:
        metadata_record["label"] = label
    metadata = (json.dumps(metadata_record, indent=2, sort_keys=True) + "\n").encode("utf-8")
    write_artifacts(image_path, image, metadata, force)
    return image_path, image_path.with_suffix(".json")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pdf", type=Path)
    parser.add_argument("outdir", type=Path)
    parser.add_argument("--page", type=int, required=True, help="one-based page number")
    parser.add_argument("--dpi", type=int, default=300)
    parser.add_argument("--crop", type=parse_crop, help="PDF points: x0,y0,x1,y1")
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    try:
        image_path, metadata_path = render(
            args.pdf, args.outdir, args.page, args.dpi, args.crop, args.force
        )
    except (FileNotFoundError, FileExistsError, ValueError) as exc:
        parser.error(str(exc))
    print(image_path)
    print(metadata_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
