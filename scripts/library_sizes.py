#!/usr/bin/env python3
"""Generate the paper's table of package sizes from the Lean sources of the repository.

A package is a top-level directory with a `lakefile.toml`. Its sources are the modules of its
`lean_lib`s that `lake build` builds: the root modules (the library name, or its `roots`) and
every module of the package that they import, transitively. Examples inside the library (such as
`Voter/Examples.lean`) count; `Audit.lean` (axiom prints, not part of the library), blueprints,
standalone LaTeX proofs, modules that no root imports and everything under `.lake/` do not. A
`lean_lib` with custom `globs` is not supported (the script stops).

The counts are textual, on each file:
- lines: all lines of the file, comments and blank lines included (as `wc -l`);
- theorems: declarations introduced by `theorem` or `lemma`;
- defs: declarations introduced by `def`, `abbrev`, `structure`, `inductive`, `class` (also
  `class inductive`, counted once), `instance`, `opaque` or `irreducible_def`.
A declaration is counted when its keyword starts a line after comments are removed (`--`,
nested `/- -/`, doc and module comments), possibly after attributes `@[...]`, the modifiers
`private`, `protected`, `public`, `noncomputable`, `nonrec`, `partial`, `unsafe`, `local`,
`scoped`, and prefixes `set_option ... in` or `open ... in`; every modifier counts the same.
`example`, `alias`, `notation`, `macro`, `syntax`, `elab` and `deriving instance` are not
counted.

The one-line main result of each package is in PACKAGES below, which also fixes the order of the
rows: the shared layer, then the packages in the order of the case studies of the paper, then
`crn`. The descriptions are LaTeX (ASCII only, for pdfLaTeX) and may refer to labels of the paper.

Usage:
    python3 scripts/library_sizes.py [--table OUT.tex]
    python3 scripts/library_sizes.py --check

Without `--table` the table is printed. `--check` fails if a package has no description, a
description names a package that does not exist, or a description is not ASCII or has an
unbalanced `$`. The table needs the packages `booktabs` and `array`, and a command `\\code`
(typewriter text) for package names.
"""
import argparse
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Package directory -> main result (LaTeX), in the order of the rows.
PACKAGES = {
    "dynamics": r"shared finite probability layer (Section~\ref{sec:layer})",
    "voter": r"Hassin--Peleg; consensus times on $K_n$ and any graph",
    "moran": r"isothermal theorem; push vs pull; the star amplifier",
    "plurality": r"$k$ colors: vanishing bias, any start; lower bounds",
    "median": r"2-Choices: any start, adversary, expanders, $k$ colors",
    "undecided": r"majority; $k$ colors, upper and lower bounds",
    "averaging": r"convergence and its rate; community reconstruction",
    "epidemics": r"Reed--Frost, percolation, COBRA, SIR; rumors on $K_n$",
    "crn": r"CRNs as protocols; stable computation; exact majority",
}

THEOREM_KEYWORDS = ["theorem", "lemma"]
DEF_KEYWORDS = ["def", "abbrev", "structure", "inductive", "class", "instance", "opaque",
                "irreducible_def"]
MODIFIERS = ["private", "protected", "public", "noncomputable", "nonrec", "partial", "unsafe",
             "local", "scoped"]
DECL = re.compile(
    r"^\s*(?:(?:set_option\s+\S+\s+\S+|open\s+[^\n]*?)\s+in\s+)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:" + "|".join(MODIFIERS) + r")\s+)*"
    r"(" + "|".join(THEOREM_KEYWORDS + DEF_KEYWORDS) + r")(?![\w'!?.])",
    re.M)
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", re.M)


def packages():
    """Top-level directories with a `lakefile.toml`, by name."""
    return sorted(p.parent.name for p in ROOT.glob("*/lakefile.toml"))


def strip_comments(text):
    """The text with comments replaced by spaces, keeping the line breaks."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def modules(pkg):
    """Paths of the Lean files that `lake build` builds for the package `pkg`."""
    d = ROOT / pkg
    with open(d / "lakefile.toml", "rb") as f:
        libs = tomllib.load(f).get("lean_lib", [])
    if not libs:
        sys.exit(f"{pkg}: no lean_lib in lakefile.toml")
    todo = []
    for lib in libs:
        if "globs" in lib:
            sys.exit(f"{pkg}: lean_lib {lib['name']} has custom globs, which are not supported")
        todo += lib.get("roots", [lib["name"]])
    seen = {}
    while todo:
        m = todo.pop()
        path = d / (m.replace(".", "/") + ".lean")
        if m in seen or not path.is_file():  # modules of other packages
            continue
        seen[m] = path
        todo += IMPORT.findall(strip_comments(path.read_text(encoding="utf-8")))
    return sorted(seen.values())


def count(pkg):
    """Lines, theorems and defs of the package `pkg`."""
    lines = thms = defs = 0
    for path in modules(pkg):
        text = path.read_text(encoding="utf-8")
        lines += len(text.splitlines())
        for kw in DECL.findall(strip_comments(text)):
            if kw in THEOREM_KEYWORDS:
                thms += 1
            else:
                defs += 1
    return lines, thms, defs


def check():
    """Problems of PACKAGES against the repository."""
    problems = []
    have = packages()
    for p in have:
        if p not in PACKAGES:
            problems.append(f"package {p} has no description in PACKAGES")
    for p, desc in PACKAGES.items():
        if p not in have:
            problems.append(f"PACKAGES describes {p}, which is not a package")
        if any(ord(c) > 127 for c in desc):
            problems.append(f"{p}: non-ASCII characters in the description (use LaTeX)")
        if desc.replace(r"\$", "").count("$") % 2:
            problems.append(f"{p}: unbalanced $ in the description")
    return problems


def tex_name(pkg):
    return r"\code{" + pkg.replace("_", r"\_") + "}"


CAPTION = (r"Sizes of the packages, in the Lean modules that \code{lake build} builds: all lines "
           r"(comments and blank lines included); theorems (\code{theorem}, \code{lemma}); "
           r"definitions (\code{def}, \code{abbrev}, \code{structure}, \code{inductive}, "
           r"\code{class}, \code{instance}), with any modifiers; \code{example} blocks are not counted.")


def table():
    rows, total = [], [0, 0, 0]
    for p in PACKAGES:
        n = count(p)
        total = [a + b for a, b in zip(total, n)]
        rows.append(f"{tex_name(p)} & {PACKAGES[p]} & " + " & ".join(map(str, n)) + r" \\")
    out = [
        "% Generated by scripts/library_sizes.py from the Lean sources of the repository; "
        "do not edit.",
        "% Needs \\usepackage{booktabs,array} and a command \\code for package names.",
        r"\begin{table}[t]",
        # One line per row on a 16 cm text width: narrower gaps, and the main result wraps if
        # it is longer than about 55 characters.
        r"\centering\setlength{\tabcolsep}{4pt}",
        r"\begin{tabular}{@{}l>{\raggedright\arraybackslash}p{9.1cm}rrr@{}}",
        r"\toprule",
        r"Package & Main result & Lines & Theorems & Defs \\",
        r"\midrule",
        *rows,
        r"\midrule",
        r"total & & " + " & ".join(map(str, total)) + r" \\",
        r"\bottomrule",
        r"\end{tabular}",
        r"\caption{" + CAPTION + "}",
        r"\label{tab:sizes}",
        r"\end{table}",
    ]
    tex = "\n".join(out) + "\n"
    bad = sorted({c for c in tex if ord(c) > 127})
    if bad:
        sys.exit(f"non-ASCII characters {bad} in the table; use LaTeX in PACKAGES")
    return tex


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--table", help="write the LaTeX table here instead of stdout")
    ap.add_argument("--check", action="store_true",
                    help="only check that every package has a description and every "
                         "description a package")
    args = ap.parse_args()

    problems = check()
    if args.check:
        for p in problems:
            print(p, file=sys.stderr)
        print(f"{len(packages())} packages, {len(PACKAGES)} descriptions: "
              + ("ok" if not problems else f"{len(problems)} problems"), file=sys.stderr)
        sys.exit(1 if problems else 0)
    if problems:
        sys.exit("\n".join(problems) + "\n(see --check)")
    tex = table()
    if args.table:
        Path(args.table).write_text(tex, encoding="utf-8")
    else:
        sys.stdout.write(tex)


if __name__ == "__main__":
    main()
