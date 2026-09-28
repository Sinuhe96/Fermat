#!/usr/bin/env python3
"""Print-defect sweep over the signed region records  (read-only, host-side).

WHY THIS EXISTS
---------------
Two printed defects found by hand in two pages (Q-005 on p. 7, Q-006 on p. 8)
say the pp. 9-33 expansion pages need a *systematic* scan, not another leaf-by-leaf
walk into a wall. Both were the same failure mode: **one printed line carries a
coefficient that contradicts the same quantity printed elsewhere** (p. 6's
binomial side vs p. 7's factorial side; p. 7's summand vs p. 8's three pieces).
That mode is machine-detectable at the transcription level:

  * the paper re-prints the same quantity many times -- over a page break, as a
    "=" restatement, as a later "T" assembly (Q-004's C3 was printed four times);
  * re-prints should agree; when they do not, the DIFFERING tokens localise the
    defect, exactly as `triage_c3.py` localised Q-004's items;
  * the pages are labelled (7), (8), ... so the label/citation anomalies are
    already covered by `cite_index.py` and are NOT duplicated here.

WHAT IT DOES
------------
1. Loads every region line (a `\\[ ... \\]` block) in document order from the
   signed records, via the same loader `cite_index.py` uses.
2. Computes a SHAPE KEY: the line with all digits replaced by `#`, prose
   (`\\text{...}`), label tags (`\\qquad(...)`), spacing and braces removed.
   Two lines with the same shape key are "the same formula up to its numbers" --
   i.e. re-prints of one quantity.
3. Groups by shape key and reports every group whose members are NOT all
   byte-equal after normalisation: those are DRIFT CANDIDATES (with the exact
   differing tokens listed). Groups are ranked by size (more prints = more
   chances to disagree).
4. Separately lists PROSE LINES carrying a rational constant (e.g. `55/3`),
   because the one known defect of that kind (p. 33 prints `55/3` where the
   coefficients sum to `55/4`) is not a re-print drift.

IT IS A CANDIDATE GENERATOR, NOT A JUDGE. Every hit still needs the rendered PDF
(crop read) and, where the claim is computational, an exact screen -- the rules
that produced Q-005/Q-006. Exit 0 always.

RUN:  python pipeline/01-extract/defect_sweep.py [--pages 9-33] [--min-len 40]
OUT:  pipeline/01-extract/out/defect_candidates.tsv  (+ console summary)
"""
from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cite_index as ci  # noqa: E402  (the shared record loader)

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "defect_candidates.tsv")

DISPLAY = re.compile(r"\\\[(.*?)\\\]", re.S)
TEXT = re.compile(r"\\text\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}")
TAG = re.compile(r"\\(?:quad|qquad)\s*\{?\s*(?:\\text\{)?\s*\([^)]*\)\s*\}?")
RATIONAL = re.compile(r"(?<![\w{])(\d{1,3})\s*/\s*(\d{1,3})(?![\w}])")


def lines_of(latex: str):
    """The display lines of one region, in printed order."""
    return [m.group(1).strip() for m in DISPLAY.finditer(latex)]


def normalize(s: str) -> str:
    """Comparison body: prose, label tags, colour, spacing and braces dropped."""
    s = re.sub(r"\\textcolor\{[a-z]+\}\{", "", s)
    s = TAG.sub("", s)
    s = TEXT.sub("", s)
    s = s.replace("\\,", "").replace("\\ ", " ").replace("\\!", "")
    s = s.replace("\\left", "").replace("\\right", "").replace("\\;", "")
    s = s.replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", s).strip()


def shape_key(s: str) -> str:
    """The normalised line with every digit abstracted -- 'same formula, other
    numbers'.  Signs and structure are kept, so a sign or factor change survives
    into the key."""
    return re.sub(r"\d", "#", normalize(s))


def is_math(s: str) -> bool:
    n = normalize(s)
    return len(n) >= 40 and ("\\sum" in n or "\\frac" in n or "^" in n)


def prose_rationals(s: str):
    """Printed rational constants that are NOT one of the small binomial
    fractions of the expansions -- the p. 33 `\\frac{55}{3}` class (there the
    assembled coefficients sum to `55/4`).  Captures `\\frac{a}{b}` literally
    (the previous version deleted the \\frac itself and so saw nothing), plus
    bare `a/b` in prose, and keeps a hit only when a numerator or denominator is
    at least two digits or the fraction is not in the small-fraction whitelist."""
    if "\\sum" in s:
        return []
    hits = []
    for m in re.finditer(r"\\frac\{(\d{1,4})\}\{(\d{1,4})\}", s):
        hits.append(f"{m.group(1)}/{m.group(2)}")
    body = TEXT.sub(lambda m: " " + m.group(0)[6:-1] + " ", s)
    body = re.sub(r"\\frac\{\d{1,4}\}\{\d{1,4}\}", " ", body)
    hits += [f"{a}/{b}" for a, b in RATIONAL.findall(body)]
    small = {"1/2", "1/3", "1/4", "1/6", "2/3", "3/4", "2/4", "3/6", "2/6",
             "1/24", "1/12", "9/4", "1/5", "1/8", "1/7", "1/9", "1/10"}
    return [h for h in hits if h not in small]


# A summand of the expansion displays: `... h^{HE} b^{n(BI)} (n^s abck)^{K}`.
# The (HE, BI, K) triple identifies WHICH term of the triple sum a summand is,
# independently of how its coefficient is written -- so two lines carrying the
# same triple are two prints of ONE quantity, and any coefficient difference is
# the Q-005/Q-006 failure mode.
SUMMAND = re.compile(
    r"h\^\{?([^{}]*?)\}?\s*b\^\{?n\(?([^{})]*?)\)?\}?\s*\(n\^s\s*a?b?c?k?\)?\^\{?(\d+)\}?")
SUMMAND2 = re.compile(
    r"b\^\{?n\(?([^{})]*?)\)?\}?\s*h\^\{?([^{}]*?)\}?\s*\(n\^s\s*a?b?c?k?\)?\^\{?(\d+)\}?")
COEFF = re.compile(r"(?:\\frac\{[^{}]*\}\{[^{}]*\}|[-\d]+|\{[^{}]*\})")


def signatures(line: str):
    """The list of summand triples (h-exp, b-index, power-of-X) on one line."""
    n = normalize(line)
    out = []
    for m in SUMMAND.finditer(n):
        out.append((m.group(1).strip(), m.group(2).strip(), m.group(3)))
    for m in SUMMAND2.finditer(n):
        out.append((m.group(2).strip(), m.group(1).strip(), m.group(3)))
    return sorted(out)


def coefficients(line: str):
    """The text printed in front of each summand on one line: the summation
    range plus the coefficient, in printed order.  Two lines carrying the same
    summand triple can then be compared token by token."""
    n = normalize(line)
    spans = [(m.start(), m.end()) for m in SUMMAND.finditer(n)]
    spans += [(m.start(), m.end()) for m in SUMMAND2.finditer(n)]
    spans.sort()
    out, prev_end = [], 0
    for (s, e) in spans:
        head = n[prev_end:s]
        sums = list(re.finditer(r"\\sum", head))
        chunk = head[sums[-1].start():] if sums else head
        out.append(re.sub(r"\s+", " ", chunk).strip(" +-"))
        prev_end = e
    return out


def main() -> int:
    pages = None
    min_len = 40
    for i, a in enumerate(sys.argv):
        if a == "--pages" and i + 1 < len(sys.argv):
            lo, _, hi = sys.argv[i + 1].partition("-")
            pages = range(int(lo), int(hi or lo) + 1)
        if a == "--min-len" and i + 1 < len(sys.argv):
            min_len = int(sys.argv[i + 1])

    entries = []          # (page, rid, line_index, raw, norm, key)
    prose = []
    for page, rid, latex in ci.load_records():
        if pages is not None and page not in pages:
            continue
        for k, raw in enumerate(lines_of(latex)):
            n = normalize(raw)
            entries.append((page, rid, k, raw, n, re.sub(r"\d", "#", n)))
            pr = prose_rationals(raw)
            if pr:
                prose.append((page, rid, k, n, pr))

    groups = defaultdict(list)
    for e in entries:
        if len(e[4]) >= min_len:
            groups[e[5]].append(e)

    rows, multi = [], []
    for key, members in groups.items():
        if len(members) < 2:
            continue
        forms = defaultdict(list)
        for e in members:
            forms[e[4]].append(e)
        if len(forms) < 2:                       # all prints byte-equal: re-print
            continue
        multi.append(sorted(members, key=lambda e: (e[0], e[1], e[2])))
        sites = " ".join(f"P{e[0]:03d}-{e[1]}:l{e[2]}" for e in sorted(members, key=lambda e: (e[0], e[1], e[2])))
        rows.append((len(members), len(forms), "drift", sites, key))

    # --- the Q-005/Q-006 class: same summand triple, different coefficient ---
    by_sig = defaultdict(list)
    for (page, rid, k, raw, norm, _key) in entries:
        sig = signatures(raw)
        if sig:
            by_sig[tuple(sig)].append((page, rid, k, raw, tuple(coefficients(raw))))
    sig_rows = []
    for sig, members in by_sig.items():
        if len(members) < 2:
            continue
        coeffsets = {m[4] for m in members}
        if len(coeffsets) < 2:
            continue
        sites = " ".join(f"P{m[0]:03d}-{m[1]}:l{m[2]}" for m in sorted(members, key=lambda m: (m[0], m[1], m[2])))
        sig_rows.append((len(members), len(coeffsets), "summand-coeff", sites, str(sig)))
    sig_rows.sort(key=lambda r: (-r[0], -r[1]))

    rows = rows + [r for r in sig_rows if r[2] == "summand-coeff"]
    rows.sort(key=lambda r: (-r[0], -r[1]))
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("class\tprints\tdistinct\t sites\tdetail\n")
        for r in rows:
            fh.write(f"{r[2]}\t{r[0]}\t{r[1]}\t{r[3]}\t{r[4][:400]}\n")

    print(f"lines scanned      : {len(entries)}")
    print(f"candidate groups   : {len(rows)}")
    print(f"prose rationals    : {len(prose)} line(s)")
    print()
    for prints, forms, cls, sites, key in rows[:25]:
        print(f"[{cls}: {prints} prints, {forms} distinct] {sites}")
        print(f"    {key[:180]}")
    if len(rows) > 25:
        print(f"... {len(rows) - 25} more in {os.path.relpath(OUT)}")
    print()
    for page, rid, k, n, pr in prose[:40]:
        print(f"prose rational P{page:03d}-{rid}:l{k}  {pr}  :: {n[:120]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
