"""Run every sympy smoke test for chunks marked IN_PROGRESS or DONE.

Usage:
    python run_all.py

Exit 0 iff all tests pass. A failing test blocks its chunk from DONE.
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).parent


def main() -> int:
    tests = sorted(HERE.glob("test_*.py"))
    if not tests:
        print("no sympy tests found")
        return 2
    failed = []
    for t in tests:
        r = subprocess.run([sys.executable, str(t)], capture_output=True, text=True)
        print(f"--- {t.name}: {'PASS' if r.returncode == 0 else 'FAIL'} ---")
        print(r.stdout.strip())
        if r.returncode != 0:
            failed.append(t.name)
            print(r.stderr.strip()[-2000:])
    if failed:
        print(f"FAILED: {failed}")
        return 1
    print(f"all {len(tests)} sympy smoke tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
