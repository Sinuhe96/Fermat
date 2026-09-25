"""Hard-failing runtime readiness checks for the Fermat verification workspace."""

import argparse
import importlib.metadata
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

EXPECTED_LEAN = "4.35.0-rc2"
EXPECTED_LAKE = "5.0.0"
DEFAULT_PDF = Path("/workspace/source/PROOF_of_FERMAT.pdf")
DEFAULT_PIPELINE = Path("/workspace/pipeline")
DEFAULT_LEAN_ROOT = Path("/workspace/work/testproj")
DEFAULT_REQUIREMENTS = Path("/opt/fermat/requirements-container.txt")


def run(command: list[str], *, cwd: Path | None = None, timeout: int = 300) -> str:
    result = subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if result.returncode != 0:
        output = "\n".join(part.strip() for part in (result.stdout, result.stderr) if part.strip())
        raise RuntimeError(f"command failed ({result.returncode}): {' '.join(command)}\n{output}")
    return result.stdout.strip()


def parse_requirements(path: Path) -> dict[str, str]:
    if not path.is_file():
        raise FileNotFoundError(f"missing requirements lock: {path}")
    requirements = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if "==" not in line:
            raise ValueError(f"requirement must use an exact == pin: {line}")
        name, version = line.split("==", 1)
        requirements[name.strip()] = version.strip()
    return requirements


def check_commands() -> None:
    for command in ("lean", "lake", "python", "git", "rg"):
        if shutil.which(command) is None:
            raise RuntimeError(f"missing command on PATH: {command}")
    lean_version = run(["lean", "--version"])
    lake_version = run(["lake", "--version"])
    if EXPECTED_LEAN not in lean_version:
        raise RuntimeError(f"expected Lean {EXPECTED_LEAN}, got: {lean_version}")
    if EXPECTED_LAKE not in lake_version:
        raise RuntimeError(f"expected Lake {EXPECTED_LAKE}, got: {lake_version}")
    print(f"commands: OK (Lean {EXPECTED_LEAN}, Lake {EXPECTED_LAKE}, rg available)")


def check_python(requirements_path: Path) -> None:
    aliases = {"PyMuPDF": "PyMuPDF", "pypdf": "pypdf", "sympy": "sympy"}
    requirements = parse_requirements(requirements_path)
    for name, distribution in aliases.items():
        expected = requirements.get(name)
        if expected is None:
            raise RuntimeError(f"missing required pin: {name}")
        installed = importlib.metadata.version(distribution)
        if installed != expected:
            raise RuntimeError(f"expected {name} {expected}, got {installed}")
    run([sys.executable, "-m", "pip", "check"])
    print("python toolkit: OK (exact pins, pip check)")


def check_layout(pdf: Path, pipeline_root: Path, lean_root: Path) -> None:
    required = (
        pdf,
        pipeline_root / "01-extract" / "extract.py",
        pipeline_root / "01-extract" / "render_pdf.py",
        pipeline_root / "03-lean",
        lean_root / "lakefile.toml",
        lean_root / "lean-toolchain",
        lean_root / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean",
    )
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        raise FileNotFoundError("missing runtime paths:\n" + "\n".join(missing))
    if not os.access(pdf, os.R_OK):
        raise PermissionError(f"PDF is not readable: {pdf}")
    with tempfile.NamedTemporaryFile(dir=lean_root, prefix=".smoke-write-", delete=True):
        pass
    print("runtime layout: OK (mounts, Lake project, Mathlib cache, writable work volume)")


def check_pdf_tools(pdf: Path, pipeline_root: Path) -> None:
    with tempfile.TemporaryDirectory(prefix="fermat-smoke-") as temporary:
        output = Path(temporary)
        run([
            sys.executable,
            str(pipeline_root / "01-extract" / "extract.py"),
            str(pdf),
            str(output / "extract"),
            "--pages",
            "1",
        ])
        run([
            sys.executable,
            str(pipeline_root / "01-extract" / "render_pdf.py"),
            str(pdf),
            str(output / "render"),
            "--page",
            "1",
            "--dpi",
            "72",
        ])
        if not (output / "extract" / "extract_meta.json").is_file():
            raise RuntimeError("page extraction did not produce metadata")
        if not (output / "render" / "page-001-72dpi-full.json").is_file():
            raise RuntimeError("page rendering did not produce metadata")
    print("PDF tools: OK (page 1 dual extraction and deterministic rendering)")


def check_sympy() -> None:
    import sympy

    if sympy.Mod(2**5, 25) != 7:
        raise RuntimeError("Sympy modular arithmetic check failed")
    print("Sympy: OK")


def check_mathlib_compile(lean_root: Path) -> None:
    source = lean_root / "FermatSmoke.lean"
    if source.exists():
        raise FileExistsError(f"temporary smoke source already exists: {source}")
    source.write_text("import Mathlib\nexample : 2 + 2 = 4 := by norm_num\n", encoding="utf-8", newline="\n")
    try:
        run(["lake", "env", "lean", source.name], cwd=lean_root, timeout=900)
    finally:
        source.unlink(missing_ok=True)
    print("Mathlib compile: OK")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="also compile a minimal Mathlib file")
    parser.add_argument("--pdf", type=Path, default=DEFAULT_PDF)
    parser.add_argument("--pipeline-root", type=Path, default=DEFAULT_PIPELINE)
    parser.add_argument("--lean-root", type=Path, default=DEFAULT_LEAN_ROOT)
    parser.add_argument("--requirements", type=Path, default=DEFAULT_REQUIREMENTS)
    args = parser.parse_args()

    checks = (
        ("commands", lambda: check_commands()),
        ("python toolkit", lambda: check_python(args.requirements)),
        ("runtime layout", lambda: check_layout(args.pdf, args.pipeline_root, args.lean_root)),
        ("PDF tools", lambda: check_pdf_tools(args.pdf, args.pipeline_root)),
        ("Sympy", check_sympy),
    )
    for label, check in checks:
        try:
            check()
        except Exception as exc:
            print(f"SMOKE FAIL at {label}: {exc}", file=sys.stderr)
            return 1
    if args.full:
        try:
            check_mathlib_compile(args.lean_root)
        except Exception as exc:
            print(f"SMOKE FAIL at Mathlib compile: {exc}", file=sys.stderr)
            return 1
    mode = "full" if args.full else "fast"
    print(f"SMOKE PASS ({mode})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
