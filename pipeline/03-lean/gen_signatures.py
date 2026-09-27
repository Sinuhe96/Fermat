#!/usr/bin/env python3
"""Generate `SIGNATURES.md` — the call-site ABI sheet for the verified lanes.

Why this exists (measured, 2026-09-28 lane): every real compile error in
`L7-FRAG-02` … `L7-ASM` was a **call-site shape** mismatch — a producer whose
hypothesis is about a different coordinate, carries a different modulus, or
expects a congruence where the caller has a difference. Each cost a full
container round to find and another to fix, at 2.5–25 min per round here. This
file is the static check that replaces that round: read the producer's exact
binders before writing the call.

Two outputs:

* `SIGNATURES.md` — readable sheet: one section per module, every
  `theorem`/`lemma`/`def` with its **source signature verbatim** (so implicit
  binders, `ℤ`/`ZMod`/`[ZMOD …]` spellings and hypothesis order are all
  visible), plus the docstring's first line as a gloss.
* `probes/SIGNATURES.probe.lean` — a batched `#check @` file for the *same*
  declarations, to be compiled once through `proof/compile_lean.sh` into
  `probes/SIGNATURES.probe.log`: that log is what binds the names and their
  elaborated types to the pinned toolchain (the sheet itself is a text
  projection and can drift if a source line is edited by hand).

Regenerate after every DONE flip:

    python pipeline/03-lean/gen_signatures.py
    docker compose exec -T lean sh /workspace/proof/compile_lean.sh probes/SIGNATURES.probe.lean

Deliberately source-text based: it needs no container, no olean and no
Mathlib, so it runs in milliseconds and cannot be blocked by the build.
"""
from __future__ import annotations

import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent

# module root -> (chunk, human gloss); the ledger order, not alphabetical
MODULES = [
    ("Common", "shared helpers", "—"),
    ("L1", "bổ đề 1", "L1-01"),
    ("L2", "bổ đề 2", "L2-01"),
    ("L3", "bổ đề 3", "L3-01"),
    ("L4", "bổ đề 4", "L4-01"),
    ("L5", "bổ đề 5 (parts a–d)", "L5-01"),
    ("L6", "bổ đề 6", "L6-01"),
    ("L7", "bổ đề 7 — non-divisibility conclusion (S0–S6)", "L7-FRAG-01"),
    ("L7F2", "bổ đề 7 — display (a) + the (b)/(c)/(d) toolkit", "L7-FRAG-02"),
    ("L7F3", "bổ đề 7 — (19), (20) and the (a;b) symmetry", "L7-FRAG-03"),
    ("L7F4", "bổ đề 7 — (18) and (22')", "L7-FRAG-04"),
    ("L7F5", "bổ đề 7 — n ≡ 1 (mod 6)", "L7-FRAG-05"),
    ("L7F6", "bổ đề 7 — (21) and (22)", "L7-FRAG-06"),
    ("L7ASM", "bổ đề 7 — section assembly (entry point)", "L7-ASM"),
]

DECL_START = re.compile(r"^(theorem|lemma|def|abbrev|structure|noncomputable def)\s+([\w'.]+)")
NS = re.compile(r"^namespace\s+([\w'.]+)")
DOC = re.compile(r"^/--\s*(.*)$")
ENTRY = re.compile(r"^(L\d_bo_de_\d|L7_bo_de_7)$")


def declarations(path: pathlib.Path):
    """(name, full_name, signature_lines, first_doc_line, lineno) per declaration."""
    lines = path.read_text(encoding="utf-8").splitlines()
    out = []
    ns = ""
    i = 0
    in_doc = False
    while i < len(lines):
        line = lines[i]
        s = line.strip()
        # comments may contain prose like "theorem below formalises ..." — skip
        # both docstrings (`/--`) and plain block comments (`/-`), and line comments
        if in_doc:
            in_doc = not s.endswith("-/")
            i += 1
            continue
        if s.startswith("/-"):
            in_doc = not (s.endswith("-/") and s not in ("/-", "/--"))
            i += 1
            continue
        if s.startswith("--"):
            i += 1
            continue
        m = NS.match(line)
        if m:
            ns = m.group(1)
            i += 1
            continue
        d = DECL_START.match(line)
        if not d:
            i += 1
            continue
        # the closest preceding docstring block (first non-empty line inside it)
        gloss = ""
        j = i - 1
        if j >= 0 and lines[j].strip().endswith("-/"):
            k = j
            while k >= 0 and not lines[k].lstrip().startswith("/--"):
                k -= 1
            # first sentence of the docstring, joined across lines
            words: list[str] = []
            for cand in lines[k : j + 1]:
                s = cand.strip()
                if s.startswith("/--"):
                    s = s[3:]
                if s.endswith("-/"):
                    s = s[:-2]
                s = s.strip()
                if not s or s in ("-",):
                    if words:
                        break
                    continue
                words.append(s)
                if len(" ".join(words)) > 90 or s.endswith("."):
                    break
            gloss = " ".join(words).strip()
            if len(gloss) > 120:
                gloss = gloss[:117].rstrip() + "…"
        sig = []
        j = i
        while j < len(lines):
            cur = lines[j]
            cut = cur.find(":=")
            if cut != -1:
                sig.append(cur[:cut].rstrip())
                break
            if cur.strip() in ("by", "where", "deriving"):
                break
            sig.append(cur.rstrip())
            if j > i + 40:  # safety: no declaration here is that long
                break
            j += 1
        out.append((d.group(2), f"{ns}.{d.group(2)}" if ns else d.group(2),
                    "\n".join(sig), gloss, i + 1))
        i = j + 1
    return out


def main() -> int:
    head = ["""# SIGNATURES.md — call-site ABI sheet for the verified lanes (generated)

Generated by `pipeline/03-lean/gen_signatures.py` from the module sources; do
not hand-edit — edit the Lean source and regenerate. Signatures below are the
**source text** of each declaration's header (implicit binders, `ℤ` / `ZMod` /
`[ZMOD …]` spellings and hypothesis order preserved verbatim).

## How to use — read this before writing a call site

The 2026-09-28 lane (`L7-FRAG-02` … `L7-ASM`) spent **every** one of its error
rounds on call-site *shape*: a producer whose `¬ n ∣ x` hypothesis is about a
different coordinate than the caller assumes, a hypothesis wanted at modulus
`n` while the caller has it at `n²`, or a congruence wanted where the caller
has a difference. Check these four things on the producer's header line before
writing the call:

1. **Coordinate.** Each `¬ (n : ℤ) ∣ <expr>` says which of `a`/`b`/`c` — the
   conclusion does *not* imply which one it takes (e.g. `L7_step_S5b` concludes
   `¬ n ∣ c^n + a^n` but takes `ha : ¬ n ∣ a`).
2. **Modulus.** `[ZMOD (n : ℤ)]` vs `[ZMOD (n ^ 2 : ℤ)]`: take an author step's
   inputs at the modulus *its own printed line* uses; the printed (c) is mod
   `n`, (b) is mod `n²`.
3. **Form.** Congruence `x ≡ y`, "difference" `x - y ≡ 0`, or divisibility
   `n ∣ x`. They are interchangeable mathematically but *not* syntactically:
   `rw`/`exact` need the stated form (`Int.modEq_iff_dvd.mp/.mpr`,
   `Int.modEq_zero_iff_dvd.mp/.mpr` are the bridges).
4. **Orientation of sums/products.** `b^{3n} + c^{3n}` ≠ `c^{3n} + b^{3n}` to
   plain `simpa`; pass `simpa [add_comm]` / `[mul_comm]` explicitly.

Arguments are positional: pass them in the printed order (or name the implicit
ones, e.g. `(X := b) (Y := a)`).

## Entry points (what a new lane should cite)

| module | assembly theorem | proves |
|---|---|---|"""]
    probe = ["-- Batched `#check` for every declaration in SIGNATURES.md.",
             "-- Regenerate with: python pipeline/03-lean/gen_signatures.py",
             "-- Compile:  sh /workspace/proof/compile_lean.sh probes/SIGNATURES.probe.lean",
             "-- The log (probes/SIGNATURES.probe.log) is what binds these names/types",
             "-- to the pinned toolchain; a `#check` list is trustworthy only if it ran.",
             "import Mathlib"] + [f"import {mod}.Basic" for mod, _, _ in MODULES]
    body: list[str] = []
    counts: list[tuple[str, str, int]] = []
    for mod, gloss, chunk in MODULES:
        path = HERE / mod / "Basic.lean"
        if not path.exists():
            continue
        decls = declarations(path)
        counts.append((mod, gloss, len(decls)))
        for name, full, sig, doc, ln in decls:
            if ENTRY.match(name):
                head.append(f"| `{mod}` | `{full}` | {gloss} |")
        body.append(f"\n## `{mod}` — {gloss}  (chunk {chunk}, {len(decls)} declarations)\n")
        body.append(f"Source: `pipeline/03-lean/{mod}/Basic.lean`\n")
        for name, full, sig, doc, ln in decls:
            body.append(f"### `{full}`  — `{mod}/Basic.lean:{ln}`")
            if doc:
                body.append(f"*{doc}*")
            body.append("```lean")
            body.append(sig)
            body.append("```\n")
            probe.append(f"#check @{full}")
    probe.append("")
    head.append("")
    head.append("The full per-module list follows. Non-entry declarations are "
                "support: reuse them, but cite an entry point where one exists.\n")
    head.append("## Declarations by module\n")
    tail = ["\n## Module inventory\n\n| module | lane | declarations |\n|---|---|---|"]
    for mod, gloss, n in counts:
        tail.append(f"| `{mod}` | {gloss} | {n} |")
    tail.append("\n## Pin check\n\n"
                "`probes/SIGNATURES.probe.lean` + `probes/SIGNATURES.probe.log` "
                "(compiled once through `proof/compile_lean.sh`; EXIT 0 means every "
                "name above exists with the type the sheet shows).\n")
    tail.append("""## Call-site traps observed in this repo

- `Int.gcd_comm` does not exist; `IsCoprime` exponents are implicit
  (`h.pow_left (m := 2)`, never `h.pow 2 1`).
- `(n ^ 2 : ℤ)` *is* `(↑n) ^ 2` — no `Nat.cast_pow` bridge needed.
- prefix `-` binds tighter than `^`: write `-((c ^ n) ^ k)`.
- `rwa [h] at X` = `rw` + `assumption`; fails when `X` is a divisibility and
  the goal is a `≡`.
- `Nat.dvd_prime` is divisor-side; use `Nat.Prime.dvd_iff_eq` for `p ∣ n` with
  `n` prime.
- `omega` cannot read `Nat.Prime` (add `hn.two_le`) and cannot do nonlinear
  exponent identities.
- `pow_add` emits `x ^ (m + n)`; state ℕ exponent identities in that order.
- `dvd_add` needs both summands in the goal's shape — assemble with an explicit
  `ring` identity instead of guessing the argument order.
""")
    (HERE / "SIGNATURES.md").write_text("\n".join(head + body + tail),
                                        encoding="utf-8", newline="\n")
    (HERE / "probes" / "SIGNATURES.probe.lean").write_text("\n".join(probe) + "\n",
                                                           encoding="utf-8", newline="\n")
    total = sum(n for _, _, n in counts)
    print(f"SIGNATURES.md: {total} declarations over {len(counts)} modules")
    print(f"probes/SIGNATURES.probe.lean: {total} #check lines")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
