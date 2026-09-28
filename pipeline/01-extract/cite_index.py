#!/usr/bin/env python3
"""Label/citation index over the signed region records  (read-only, host-side).

WHY THIS EXISTS
---------------
Lean's kernel cannot certify a circular proof: imports are acyclic and a
declaration cannot reference itself.  So a circularity in the AUTHOR's chain
cannot reach the kernel as a compiling theorem -- it can only enter through US,
by encoding an author step with a hypothesis that the print establishes only
LATER (or as the conclusion itself).  That is a transcription-boundary error
(class F4/F3), and its signature is visible in the paper's citation structure:

  FORWARD      a step cites a label that is printed after it   -> prime suspect
  REUSED       one label printed twice, contents DIFFERING     -> label collision
                 (`P027-R3` prints p. 6's (7) content as (10))
  DANGLING     a label cited that is never printed anywhere    -> does not exist
                 (labels (16) and (26), cited on p. 32)
  DOUBLE       one label printed twice, contents IDENTICAL     -> a reprint, not
                 a second step (the `P008-R1/R2/R3` trap); NOT a finding

Ordering is (page, region index, line index) from the signed records, which is
document order.  A citation is "forward" when its site precedes the FIRST
printed occurrence of its label.  Exact-label matching is deliberate: `(7)` and
`(10)` at `P027-R3` are the same token, and that collision is the point.

RUN:  python pipeline/01-extract/cite_index.py            (exit 0 always)
OUT:  pipeline/01-extract/out/citations.tsv
"""
import glob
import os
import re
import sys
from itertools import combinations

try:
    import yaml
except ImportError:  # pragma: no cover
    sys.exit("need pyyaml (host python has it; the container venv does not)")

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "citations.tsv")

# A label: `(3)`, `(1')`, `(1'')`, `(26)`.  Vietnamese prose uses plain parens
# for other purposes, so classification uses the syntax the records actually
# exhibit (measured over pp. 6-33):
#   DEFINITION  the label names the display it terminates -- either \quad/\qquad
#               tagged (`... \qquad (14)`, `\qquad{\text{(10)}}`) or attached to
#               a congruence (`... \pmod{n^{2s+1}}\ (7) \]`).
#   CITATION    prose reference, always carrying a Vietnamese cue in the ~60
#               characters before the token (`Từ (11) suy ra`, `sử dụng (7)`,
#               `(PT (17) và PT(17'))`, `\text{Từ (16), (28), ...}`).
LABEL = re.compile(r"\(\s*(\d{1,2}(?:'{0,2}))\s*\)")
TAG_CUE = re.compile(r"\\(?:quad|qquad)\s*\{?\s*(?:\\text\{)?\s*$")
# "attached to a display": a congruence OR a divisibility statement.  Measured
# need: pp. 3-4 label (4')-(6'') off `\not\vdots` statements, no `mod` nearby.
ATTACH = re.compile(r"(?:\\pmod|\\mathrm\{mod|mod|\\vdots)")
# The citation cue must be NEAR the token: p. 17 defines (12) in a line that
# also contains `Từ (11)`, so a 60-char window wrongly reads it as a citation.
CITE_CUE = re.compile(r"Từ|từ|theo|và|với|sử dụng|dùng|Kết hợp|kết hợp|áp dụng|Do\b|PT")
CUE_WIN = 16
# remainder of the line after the token: punctuation / closers only
QUIET = re.compile(r"^[\s.,;)\]}]*$|^[\s.,;)\]}]*\\?\]\s*$")


def norm(s):
    """Body for comparing two prints of one label: emphasis and prose dropped,
    so `\\text{Vậy ta có } X (17)` and `\\Rightarrow X (17)` compare equal."""
    s = re.sub(r"\\textcolor\{[a-z]+\}\{", "", s)
    s = re.sub(r"\\text\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}", "", s)
    s = s.replace("\\Rightarrow", "").replace("\\,", "")
    s = s.replace("\\ ", " ").replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", s).strip()


def parse_strict(path):
    """Strict YAML.  Returns (page, [(rid, latex), ...]) or None if the record
    is not valid YAML (some `notes:` values are unquoted and contain ': ')."""
    try:
        with open(path, encoding="utf-8") as fh:
            doc = yaml.safe_load(fh)
    except Exception:
        return None
    page = doc.get("page")
    out = []
    for reg in doc.get("regions") or []:
        out.append((reg.get("id"), (reg.get("latex") or "").rstrip("\n")))
    return page, out


def parse_fallback(path):
    """Line-based reader for the fixed region-record layout; used when the
    record is not strict YAML.  Only reads `page:`, `- id:` and `latex: |`."""
    page, out = None, []
    rid, lines, indent, in_latex = None, [], None, False
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            line = raw.rstrip("\n")
            if in_latex:
                if not line.strip():
                    lines.append("")
                    continue
                if len(line) - len(line.lstrip(" ")) > indent:
                    lines.append(line.strip())
                    continue
                out.append((rid, "\n".join(lines)))
                lines, in_latex = [], False
            if not line.strip():
                continue
            m = re.match(r"^page:\s*(\d+)", line)
            if m:
                page = int(m.group(1))
                continue
            m = re.match(r"^\s*- id:\s*(\S+)", line)
            if m:
                if rid is not None and lines:
                    out.append((rid, "\n".join(lines)))
                rid, lines = m.group(1), []
                continue
            m = re.match(r"^(\s*)latex:\s*\|", line)
            if m:
                indent, in_latex = len(m.group(1)), True
                continue
    if rid is not None and lines:
        out.append((rid, "\n".join(lines)))
    return page, out


def load_records():
    """Every region record as (page, rid, latex), with a cross-check of the two
    parsers so the tolerant path cannot silently disagree with YAML."""
    recs, tolerated = [], []
    for path in sorted(glob.glob(os.path.join(HERE, "regions", "p*.yml"))):
        strict = parse_strict(path)
        fallback = parse_fallback(path)
        name = os.path.basename(path)
        if strict is None:
            tolerated.append(name)
            chosen = fallback
        else:
            if strict != fallback:
                print(f"WARNING: parsers disagree on {name}; using strict YAML")
            chosen = strict
        page, regions = chosen
        if page is None:
            print(f"WARNING: no page number in {name}")
        for rid, latex in regions:
            recs.append((page, rid, latex))
    if tolerated:
        print(f"NOTE: not strict YAML (fallback parser): {', '.join(tolerated)}")
    return recs


def load_sites():
    """Every line of every signed region, in document order."""
    sites = []
    for page, rid, latex in load_records():
        for l_i, line in enumerate(latex.split("\n")):
            sites.append((page, 0, l_i, rid, line))
    # region order inside a page follows R1, R2, ... as printed
    sites.sort(key=lambda t: (t[0], str(t[3]), t[2]))
    return sites


STATEMENT_LABELS = {"1"}   # equation (1) is named inline in prose on p. 1
                           # (`... x^n + y^n = z^n (1)`) and cited as `PT (1)`


def classify(line, m):
    """'def' | 'def?' | 'cite' for the label token at m in `line`.
    'def?' = definition by the congruence rule that is NOT display-final, i.e.
    a case to eyeball (the tool prints every one)."""
    pre = line[max(0, m.start() - 60):m.start()]
    near = line[max(0, m.start() - CUE_WIN):m.start()]
    post = line[m.end():]
    if TAG_CUE.search(pre):
        return "def"
    if ATTACH.search(pre) and not CITE_CUE.search(near):
        return "def" if QUIET.match(post) else "def?"
    # display-final with no citation cue: p. 18 tags `.../(2(h-b^n)^2) (13) ]`
    # off a plain fraction, no modulus anywhere on the line
    if QUIET.match(post) and not CITE_CUE.search(near):
        return "def"
    return "cite"


def main():
    sites = load_sites()
    defs, cites, ambig = [], [], []
    for order, (page, r_i, l_i, rid, line) in enumerate(sites):
        for m in LABEL.finditer(line):
            kind = classify(line, m)
            rec = {"order": order, "label": m.group(1), "page": page, "rid": rid,
                   "line": l_i, "text": line.strip(), "kind": kind}
            (defs if kind != "cite" else cites).append(rec)
            if kind == "def?":
                ambig.append(rec)

    print(f"sites scanned: {len(sites)} lines, {len(defs)} definitions "
          f"({len(ambig)} flagged), {len(cites)} citations")

    first_def, by_label = {}, {}
    for d in defs:
        first_def.setdefault(d["label"], d)
        by_label.setdefault(d["label"], []).append(d)

    findings, rewrap = [], []
    # 1. repeated definitions of one label -- identical text is a harmless
    #    reprint; one print containing the other is a restatement (p. 30 prints
    #    (17) alone, then (17) and (17') together); anything else is a collision
    for lab, ds in sorted(by_label.items(), key=lambda kv: kv[0]):
        if len(ds) < 2:
            continue
        bodies = [norm(d["text"]) for d in ds]
        sites_s = ", ".join(f"p{d['page']} {d['rid']} L{d['line']}" for d in ds)
        if len(set(bodies)) == 1:
            findings.append(("DOUBLE", lab, sites_s,
                             "identical text (reprint, not a second step)"))
        elif any(a in b or b in a for a, b in combinations(bodies, 2)):
            rewrap.append((lab, sites_s,
                           "one print contains the other (restatement)"))
        else:
            findings.append(("REUSED", lab, sites_s,
                             "CONTENTS DIFFER -> label collision"))
    # 2. definition order, in document order: a label that appears as a
    #    definition *below* the running maximum is either a reprint (base ==
    #    max) or a collision (base < max, e.g. p. 27 printing (10) again after
    #    (25)).  Primed sub-labels (7', 16'') are exempt.
    seen_max = 0
    for d in defs:
        lab = d["label"]
        if "'" in lab or lab in STATEMENT_LABELS:
            continue
        n = int(lab)
        if n < seen_max:
            findings.append(("ORDER", lab,
                             f"printed at p{d['page']} {d['rid']} L{d['line']}",
                             f"counter already at {seen_max} -> reuse/collision"))
        seen_max = max(seen_max, n)
    # 3. citations with no printed definition, and citations printed too early
    for c in cites:
        if c["label"] in STATEMENT_LABELS:
            continue
        fd = first_def.get(c["label"])
        if fd is None:
            findings.append(("DANGLING", c["label"],
                             f"p{c['page']} {c['rid']} L{c['line']}",
                             norm(c["text"])[:100]))
        elif c["order"] < fd["order"]:
            findings.append(("FORWARD", c["label"],
                             f"cite p{c['page']} {c['rid']} L{c['line']} "
                             f"< def p{fd['page']} {fd['rid']} L{fd['line']}",
                             norm(c["text"])[:100]))

    rows = [("DEF" if d["kind"] == "def" else "DEF?", d["label"], d["page"],
             d["rid"], d["line"], d["text"][:160]) for d in defs]
    rows += [("CITE", c["label"], c["page"], c["rid"], c["line"], c["text"][:160])
             for c in cites]
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("kind\tlabel\tpage\tregion\tline\ttext\n")
        for r in rows:
            fh.write("\t".join(str(x) for x in r) + "\n")

    print(f"distinct labels: {len(by_label)} defined, "
          f"{len({c['label'] for c in cites})} cited")
    print("-- DEFINITION CHAIN (label: first printed) --")
    for lab, d in sorted(first_def.items(), key=lambda kv: kv[1]["order"]):
        n_cite = sum(1 for c in cites if c["label"] == lab)
        print(f"   ({lab}) p{d['page']} {d['rid']} L{d['line']}   cited {n_cite}x")
    print("-- ANOMALIES --")
    order = {"FORWARD": 0, "REUSED": 1, "ORDER": 2, "DANGLING": 3, "DOUBLE": 4}
    for kind, lab, site, note in sorted(findings, key=lambda f: (order[f[0]], f[1])):
        print(f"  {kind:9s} ({lab}) {site} -- {note}")
    if not findings:
        print("  (none)")
    if rewrap:
        print("-- LABEL PRINTED AGAIN, HARMLESS (not a finding) --")
        for lab, sites_s, note in rewrap:
            print(f"  REWRAP    ({lab}) {sites_s} -- {note}")
    if ambig:
        print("-- AMBIGUOUS (congruence rule, not display-final; verify by hand) --")
        for a in ambig:
            print(f"   ({a['label']}) p{a['page']} {a['rid']} L{a['line']}: "
                  f"{norm(a['text'])[:120]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
