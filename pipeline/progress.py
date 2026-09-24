"""Progress dashboard generator: single source of truth for where we are.

Usage:
    python progress.py [--check] [--write PROGRESS.md]

Reads (never writes, except PROGRESS.md with --write):
    pipeline/02-chunks/status.tsv ....... chunk checkpoint ledger
    pipeline/02-chunks/chunks/*.yml ..... per-chunk records (depends_on, status)
    pipeline/BLOCKERS.md ................ obstacle log (counts OPEN items)
    pipeline/05-feedback/queries/*.md ... author queries (counts OPEN items)

Exit codes:
    0 — dashboard generated; counts consistent (ledger matches chunk files).
    1 — INCONSISTENT: status.tsv disagrees with a chunk file, a depends_on
        points at an unknown chunk, or a dependency cycle exists. Fix the
        ledger before trusting the dashboard.

The generated PROGRESS.md is a read-only snapshot for humans. The .tsv,
the chunk files, BLOCKERS.md and the query files are the editable sources.
"""
import argparse
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CHUNKS_DIR = HERE / "02-chunks" / "chunks"
STATUS_TSV = HERE / "02-chunks" / "status.tsv"
BLOCKERS = HERE / "BLOCKERS.md"
QUERIES_DIR = HERE / "05-feedback" / "queries"

STATUSES = ("TODO", "IN_PROGRESS", "BLOCKED", "DONE")


def parse_status_tsv() -> tuple[list[str], list[dict[str, str]]]:
    lines = STATUS_TSV.read_text(encoding="utf-8").splitlines()
    header = lines[0].split("\t")
    return header, [dict(zip(header, line.split("\t"))) for line in lines[1:] if line.strip()]


def parse_chunk(path: Path) -> dict:
    """Minimal YAML-subset parser: flat `key: value` + `depends_on: [..]`."""
    record: dict = {"_file": path.name}
    text = path.read_text(encoding="utf-8")
    for line in text.splitlines():
        if re.match(r"^\s+#", line) or not line.strip() or line.startswith((" ", "\t")):
            continue
        m = re.match(r"^([A-Za-z_]+):\s*(.*)$", line)
        if m:
            record[m.group(1)] = m.group(2).strip()
    deps = record.get("depends_on", "[]")
    record["depends_on"] = [d.strip() for d in deps.strip("[]").split(",") if d.strip()]
    return record


def count_blockers() -> tuple[int, list[str]]:
    if not BLOCKERS.exists():
        return 0, []
    ids = re.findall(r"^##\s+(B-\d+).*?\[OPEN\]", BLOCKERS.read_text(encoding="utf-8"),
                     re.MULTILINE)
    return len(ids), ids


def count_queries() -> tuple[int, int, list[str]]:
    if not QUERIES_DIR.exists():
        return 0, 0, []
    files = sorted(p for p in QUERIES_DIR.glob("Q-*.md") if "template" not in p.stem.lower())
    open_ids = [f.stem for f in files if "[OPEN]" in f.read_text(encoding="utf-8")[:2000]]
    return len(files), len(open_ids), open_ids


def check_consistency(rows: list[dict], chunks: dict[str, dict]) -> list[str]:
    errors = []
    ledger_ids = {r["chunk"] for r in rows}
    for cid, rec in chunks.items():
        if cid not in ledger_ids:
            errors.append(f"chunk file {rec['_file']} has no status.tsv row")
        elif rec.get("status", "") != next(r["status"] for r in rows if r["chunk"] == cid):
            errors.append(f"status mismatch for {cid}: tsv vs chunk file")
    for r in rows:
        if r["chunk"] not in chunks:
            errors.append(f"status.tsv row {r['chunk']} has no chunk file")
        if r["status"] not in STATUSES:
            errors.append(f"unknown status '{r['status']}' for {r['chunk']}")
    for cid, rec in chunks.items():
        for dep in rec["depends_on"]:
            if dep not in chunks:
                errors.append(f"{cid} depends on unknown chunk {dep}")
    # cycle detection over depends_on
    visited: dict[str, int] = {}

    def visit(node: str, stack: list[str]) -> None:
        state = visited.get(node, 0)
        if state == 2:
            return
        if state == 1:
            errors.append("dependency cycle: " + " -> ".join([*stack, node]))
            return
        visited[node] = 1
        for dep in chunks.get(node, {}).get("depends_on", []):
            visit(dep, [*stack, node])
        visited[node] = 2

    for cid in chunks:
        visit(cid, [])
    return errors


def blocked_by_deps(cid: str, chunks: dict, rows: dict[str, str]) -> list[str]:
    return [d for d in chunks[cid]["depends_on"] if rows.get(d) != "DONE"]


def render(rows: list[dict], chunks: dict[str, dict]) -> str:
    by_status: dict[str, list[str]] = {s: [] for s in STATUSES}
    for r in rows:
        by_status.setdefault(r["status"], []).append(r["chunk"])
    total = len(rows)
    done = len(by_status.get("DONE", []))
    pct = 100 * done // total if total else 100
    bar = "#" * (pct // 5) + "-" * (20 - pct // 5)
    rows_by_id = {r["chunk"]: r["status"] for r in rows}
    n_blockers, blocker_ids = count_blockers()
    n_queries, n_open_q, open_q = count_queries()

    out = []
    out.append("# Progress — FLT formalization")
    out.append("")
    out.append(f"Overall: [{bar}] {done}/{total} DONE ({pct}%)")
    out.append("")
    out.append("| Status | Count | Chunks |")
    out.append("|---|---|---|")
    for s in STATUSES:
        ids = ", ".join(sorted(by_status.get(s, []))) or "—"
        out.append(f"| {s} | {len(by_status.get(s, []))} | {ids} |")
    out.append("")
    out.append("## Ready to start (deps satisfied, not DONE)")
    ready = [cid for cid in chunks
             if rows_by_id.get(cid) in ("TODO", "IN_PROGRESS")
             and not blocked_by_deps(cid, chunks, rows_by_id)]
    out.append("")
    out.append(", ".join(sorted(ready)) if ready else "— none —")
    out.append("")
    out.append("## Waiting on dependencies")
    out.append("")
    waiting = [(cid, blocked_by_deps(cid, chunks, rows_by_id)) for cid in chunks
               if rows_by_id.get(cid) in ("TODO", "IN_PROGRESS")
               and blocked_by_deps(cid, chunks, rows_by_id)]
    if waiting:
        for cid, deps in sorted(waiting):
            out.append(f"- {cid} waits on {', '.join(deps)}")
    else:
        out.append("— none —")
    out.append("")
    out.append(f"## Obstacles: {n_blockers} OPEN ({', '.join(blocker_ids) if blocker_ids else 'none'})")
    out.append("See `pipeline/BLOCKERS.md`.")
    out.append("")
    out.append(f"## Author queries: {n_open_q} OPEN of {n_queries} total"
              + (f" ({', '.join(open_q)})" if open_q else ""))
    out.append("See `pipeline/05-feedback/`.")
    out.append("")
    out.append("_Generated by `pipeline/progress.py`. Edit the sources "
               "(status.tsv, chunk files, BLOCKERS.md, queries/) — not this file._")
    out.append("")
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true",
                    help="verify consistency only, print dashboard to stdout")
    ap.add_argument("--write", default=None, metavar="PROGRESS.md",
                    help="write dashboard snapshot to file")
    args = ap.parse_args()

    _, rows = parse_status_tsv()
    chunks = {}
    for path in sorted(CHUNKS_DIR.glob("*.yml")):
        rec = parse_chunk(path)
        chunks[rec.get("id", path.stem)] = rec

    errors = check_consistency(rows, chunks)
    dashboard = render(rows, chunks)
    if args.write:
        Path(args.write).write_text(dashboard, encoding="utf-8", newline="\n")
        print(f"wrote {args.write}")
    else:
        print(dashboard)
    if errors:
        print("\nINCONSISTENCIES (fix before trusting this dashboard):", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
