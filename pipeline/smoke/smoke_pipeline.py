"""Pipeline smoke test: is the MACHINE healthy? (Not: is the math right?)

Usage:
    python smoke_pipeline.py [--extract-dir DIR] [--lean-root DIR]

Checks (fail fast, first failure wins):
    1. python deps importable (pypdf, pymupdf, sympy)
    2. extract.py runs on page 1 of the PDF without crashing
    3. sympy can do a trivial modular computation
    4. lean/lake resolve on PATH (informational: warns, does not fail,
       because smoke may run on host without the toolchain)

Exit 0 = pipeline is technically alive. Exit 1 = fix the machine first.
Run BEFORE any large work.
"""
import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PDF = ROOT.parent / "PROOF_of_FERMAT.pdf"


def check_imports() -> bool:
    ok = True
    for mod in ("pypdf", "pymupdf", "sympy"):
        try:
            __import__(mod)
            print(f"import {mod}: OK")
        except ImportError:
            print(f"import {mod}: MISSING")
            ok = False
    return ok


def check_extract() -> bool:
    with tempfile.TemporaryDirectory() as tmp:
        r = subprocess.run(
            [sys.executable, str(ROOT / "01-extract" / "extract.py"),
             str(PDF), tmp],
            capture_output=True, text=True, timeout=300,
        )
        if r.returncode != 0:
            print("extract.py: FAIL")
            print(r.stderr[-2000:])
            return False
        out = Path(tmp)
        if not (out / "extract_pypdf.txt").exists() or not (out / "extract_pymupdf.txt").exists():
            print("extract.py: FAIL (missing outputs)")
            return False
        print("extract.py on full PDF: OK")
        return True


def check_sympy() -> bool:
    import sympy

    assert pow(2, 5, 25) == 7  # 32 mod 25
    print(f"sympy trivial pow: OK ({sympy.__version__})")
    return True


def check_lean() -> bool:
    import shutil

    if shutil.which("lean") and shutil.which("lake"):
        r = subprocess.run(["lean", "--version"], capture_output=True, text=True)
        print(f"lean toolchain: OK ({r.stdout.strip()})")
        return True
    print("lean toolchain: MISSING (run inside the container; not fatal for smoke)")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--extract-dir", default=None)
    parser.add_argument("--lean-root", default=None)
    parser.parse_args()
    steps = [check_imports, check_extract, check_sympy, check_lean]
    for step in steps:
        try:
            if not step():
                print(f"SMOKE FAIL at {step.__name__}")
                return 1
        except Exception as exc:  # noqa: BLE001 — smoke must report, not crash
            print(f"SMOKE FAIL at {step.__name__}: {exc}")
            return 1
    print("SMOKE PASS — pipeline is technically alive")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
