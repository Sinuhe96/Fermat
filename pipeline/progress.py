"""Progress dashboard generator: single source of truth for where we are.

Usage:
    python progress.py [--check] [--write PROGRESS.md]

Reads (never writes, except PROGRESS.md with --write):
    pipeline/02-chunks/status.tsv ....... chunk checkpoint ledger
    pipeline/02-chunks/chunks/*.yml ..... per-chunk records (depends_on, status)
    pipeline/BLOCKERS.md ................ obstacle log (counts OPEN items)
    pipeline/05-feedback/queries/*.md ... author queries (counts OPEN items)
    pipeline/01-extract/out/extract_meta.json + fidelity_report.json
        ............... extraction-run binding + per-page verdicts (evidence gate)

Exit codes:
    0 — dashboard generated; counts consistent (ledger matches chunk files)
        and every DONE chunk's evidence block verifies.
    1 — INCONSISTENT: status.tsv disagrees with a chunk file, a depends_on
        points at an unknown chunk, a dependency cycle exists, or a DONE
        chunk's evidence block is missing/stale (extraction binding, page
        verdicts, renders, lean_decls, or a `sorry` in the Lean file). Fix
        the ledger/evidence before trusting the dashboard.

The generated PROGRESS.md is a read-only snapshot for humans. The .tsv,
the chunk files, BLOCKERS.md and the query files are the editable sources.
"""
import argparse
import hashlib
import json
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
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):\s*(.*)$", line)
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


EXTRACT_OUT = HERE / "01-extract" / "out"
EVIDENCE_FIELDS = ("source_pdf_sha", "extract_run_sha", "fidelity", "renders",
                    "lean_decls", "regions")

_REGIONS_MODULE = None


def load_regions_module():
    """Load 01-extract/regions.py (record parser + freshness) via spec.

    Cached; raises on import failure (caller reports it as a gate error
    so a broken/absent toolchain fails the check, never passes it).
    """
    global _REGIONS_MODULE
    if _REGIONS_MODULE is None:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "_regions", HERE / "01-extract" / "regions.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        _REGIONS_MODULE = module
    return _REGIONS_MODULE


def parse_pages(raw: str) -> list[int]:
    inner = raw.strip().strip("[]")
    return [int(p) for p in inner.split(",") if p.strip()]


def check_evidence(rows: list[dict], chunks: dict[str, dict]) -> list[str]:
    """Machine-check the evidence block of every DONE chunk (schema criteria 6-8)."""
    errors = []
    meta_path = EXTRACT_OUT / "extract_meta.json"
    report_path = EXTRACT_OUT / "fidelity_report.json"
    if not meta_path.is_file() or not report_path.is_file():
        return ["missing 01-extract/out/extract_meta.json or fidelity_report.json "
                "(run extract.py + fidelity_check.py)"]
    meta = json.loads(meta_path.read_text(encoding="utf-8"))
    report = json.loads(report_path.read_text(encoding="utf-8"))
    run_sha = hashlib.sha256(meta_path.read_bytes()).hexdigest()
    verdicts = {p["page"]: p["verdict"] for p in report["pages"]}
    for r in rows:
        if r["status"] != "DONE":
            continue
        cid = r["chunk"]
        rec = chunks.get(cid)
        if rec is None:
            continue  # already reported by check_consistency
        for field in EVIDENCE_FIELDS:
            if not rec.get(field, "").strip():
                errors.append(f"{cid}: missing evidence field '{field}'")
        if rec.get("source_pdf_sha") and rec["source_pdf_sha"] != meta.get("sha256"):
            errors.append(f"{cid}: source_pdf_sha does not match extraction run "
                          f"({meta.get('sha256')})")
        if rec.get("extract_run_sha") and rec["extract_run_sha"] != run_sha:
            errors.append(f"{cid}: extract_run_sha stale (on-disk run is {run_sha})")
        if rec.get("fidelity") and rec["fidelity"].split()[0] != report.get("overall"):
            errors.append(f"{cid}: fidelity '{rec['fidelity']}' disagrees with report "
                          f"overall '{report.get('overall')}'")
        manual = []
        for page in parse_pages(rec.get("pdf_pages", "")):
            verdict = verdicts.get(page)
            if verdict == "MANUAL":
                manual.append(page)
            elif verdict != "OK":
                errors.append(f"{cid}: page {page} verdict {verdict!r} not cleared "
                              "(need OK, or MANUAL with the render read recorded)")
        renders = rec.get("renders", "").split()
        if manual and not renders:
            errors.append(f"{cid}: MANUAL pages {manual} require a render read ('renders')")
        for name in renders:
            if not (EXTRACT_OUT / name).is_file():
                errors.append(f"{cid}: render '{name}' missing from 01-extract/out")
            # render_pdf.py outputs carry a provenance sidecar (same stem, .json)
            elif name.startswith("page-") and not (EXTRACT_OUT / f"{Path(name).stem}.json").is_file():
                errors.append(f"{cid}: render '{name}' lacks its provenance sidecar")
        lean_rel = rec.get("lean_file", "")
        lean_path = HERE / lean_rel
        if not lean_rel or not lean_path.is_file():
            errors.append(f"{cid}: lean_file '{lean_rel}' not found")
        else:
            src = lean_path.read_text(encoding="utf-8")
            if re.search(r"\bsorry\b", src):
                errors.append(f"{cid}: lean_file '{lean_rel}' contains 'sorry' but the "
                              "chunk is DONE")
            for decl in (d.strip() for d in rec.get("lean_decls", "").split(",")):
                if decl and not re.search(rf"\b{re.escape(decl)}\b", src):
                    errors.append(f"{cid}: declaration '{decl}' not found in '{lean_rel}'")
        # Two-phase gate: vision->LaTeX region records (schema criterion 8)
        try:
            regions_mod = load_regions_module()
        except Exception as exc:
            regions_mod = None
            if not any(e.startswith("region records unavailable") for e in errors):
                errors.append(f"region records unavailable ({exc})")
        if regions_mod is not None:
            refs = [r.strip() for r in rec.get("regions", "").split(",") if r.strip()]
            parsed_refs = []
            for ref in refs:
                m = re.fullmatch(r"P(\d{3})-(.+)", ref)
                if m:
                    parsed_refs.append((ref, int(m.group(1)), m.group(2)))
                else:
                    errors.append(f"{cid}: region ref '{ref}' not found")
            covered: set[int] = set()
            for page in parse_pages(rec.get("pdf_pages", "")):
                path = regions_mod.REGIONS_DIR / f"p{page:03d}.yml"
                if not path.is_file():
                    errors.append(
                        f"{cid}: page {page} has no region record "
                        f"(pipeline/01-extract/regions/p{page:03d}.yml)")
                    continue
                try:
                    record = regions_mod.load_page_record(path)
                except Exception as exc:
                    errors.append(f"{cid}: page {page} region record unreadable ({exc})")
                    continue
                if record.get("source_pdf_sha") != meta.get("sha256"):
                    errors.append(
                        f"{cid}: page {page} region source_pdf_sha does not match "
                        f"extraction run ({meta.get('sha256')})")
                if record.get("status") != "REVIEWED":
                    errors.append(f"{cid}: page {page} region record not REVIEWED")
                elif not regions_mod.record_fresh(record):
                    errors.append(
                        f"{cid}: page {page} signoff stale "
                        "(latex edited after review)")
                region_ids = {str(r.get("id", "")) for r in record.get("regions", [])}
                for ref, ref_page, region_id in parsed_refs:
                    if ref_page == page and region_id not in region_ids:
                        errors.append(f"{cid}: region ref '{ref}' not found")
            for ref, ref_page, _region_id in parsed_refs:
                covered.add(ref_page)
            for page in parse_pages(rec.get("pdf_pages", "")):
                if page not in covered and refs:
                    errors.append(f"{cid}: regions field does not cover page {page}")
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

    errors = check_consistency(rows, chunks) + check_evidence(rows, chunks)
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
