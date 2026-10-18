#!/usr/bin/env python3
"""Generate the paper's dictionary table from home_page/_data/dictionary.yml.

The YAML file is the single source of truth for the cross-field dictionary (the website renders
the full entries). This script writes the compact LaTeX form used in the paper: one line per row
(the `paper` field of each row), grouped as in the YAML, with one column per field of `fields`
(in that order), then the relation and the Lean status, booktabs rules and citations as
`\\cite{key}`. Keys of references marked `in_paper_bib: true` are those of the paper's
bibliography; for the others it can also write BibTeX entries generated from the `references`
section of the YAML (`--bib`).

With six fields the table does not fit the 16 cm text width of a single-column A4 page, so it is
set on a page of its own in landscape (24.7 cm wide): a `table` float inside a `landscape`
environment, started with `\\afterpage` so that the current page is filled with text first. With
`pdflscape` the page is also displayed rotated in PDF viewers (pdfLaTeX, LuaLaTeX and XeLaTeX).
The table takes its number when it is typeset, that is on the page after the `\\input`.

Usage:
    python3 scripts/dictionary_tex.py [--table OUT.tex] [--bib NEW.bib] [--check-bib PAPER.bib]
    python3 scripts/dictionary_tex.py --check

Without `--table` the table is printed. With `--check-bib`, the keys marked `in_paper_bib` are
checked against the given BibTeX file, every other cited key is reported as new, and `--bib`
writes only the entries whose keys are not in that file yet (append them to it). `--check`
checks the YAML against itself and the repository: every cell of every field has a `name` (with
a description and references) or a `none`, every reference is known, cited and has an
identifier, the `paper` entries have every field and are ASCII, every Lean name is tagged in a
blueprint (CI checks those tags with `checkdecls`), every blueprint link points to a `\\label` of
that package's `content.tex`, and every roadmap ID is a target of ROADMAP.md.

`--check` also checks that every Lean name of a `correspondence` or `results` list is declared in
the sources of one of the packages that the row lists in `leanamics.packages` (a package is a
directory with a `lakefile.toml`). One of the package's `.lean` files (outside `.lake`) must
contain `theorem`, `lemma`, `def`, `abbrev`, `structure`, `inductive`, `class` or `instance`
followed by a dotted name that ends the Lean name, component by component: a declaration is
written inside its namespaces, so `Crn.Network.jumpKernel` may be declared as `def jumpKernel`
inside `namespace Network`, or as `def Network.jumpKernel` inside `namespace Crn`. The check is
textual (a commented-out declaration counts); `checkdecls` in CI resolves the blueprint tags
exactly.

The table needs the packages `booktabs`, `array`, `afterpage` and `pdflscape` (or `lscape`, which
rotates the page in print but not on screen), and `amssymb` for `\\checkmark`.
"""
import argparse
import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "home_page" / "_data" / "dictionary.yml"

# Column widths (cm), one per key of `fields` plus the relation and the Lean status, for a
# landscape A4 page with 2.5 cm margins (line width 24.7 cm), with \tabcolsep = 2.5pt: seven inner
# gaps of 5pt take about 1.23 cm. The page is 16 cm tall: at 9pt the 15 rows and the caption do
# not fit, so the table and its caption are set at 8.5/10pt. The widths were chosen by typesetting
# every cell at every width, to minimise the total height (33 lines for the 15 rows), preferring
# widths that are not at a line break. If a `paper` entry or the caption grows, check the log for
# "Float too large".
WIDTHS = {"dc": 3.25, "popgen": 3.85, "epi": 2.95, "crn": 3.6, "physics": 3.15, "social": 2.75,
          "relation": 2.65, "lean": 1.25}

LEAN_MARKS = {
    "proved": r"\checkmark",
    "definitional": r"def.",
    "results": r"results",
    "partial": r"partial",
    "roadmap": r"roadmap",
    "not-formalized": r"none",  # distinct from the `--` of a field without counterpart
}
# Keys of `leanamics` that list Lean material (empty when the status is not-formalized).
LEAN_LISTS = ["correspondence", "results", "packages", "blueprint", "roadmap"]


def load(path):
    with open(path, encoding="utf-8") as f:
        return yaml.safe_load(f)


def field_keys(data):
    """Field keys in the order of `fields`; every one needs a column width."""
    keys = [f["key"] for f in data["fields"]]
    missing = [k for k in keys if k not in WIDTHS]
    if missing:
        sys.exit(f"no column width for the fields {missing}: add them to WIDTHS")
    return keys


def cite(keys):
    return r"~\cite{" + ",".join(keys) + "}" if keys else ""


def cell(row, field):
    """Short LaTeX text of a field cell, with its paper citations."""
    paper = row.get("paper", {})
    text = paper.get(field)
    if text is None:
        data = row[field]
        text = "--" if "none" in data else data["name"]
    keys = paper.get("cite", {}).get(field, [])
    return text + cite(keys)


def lean_cell(row):
    status = row["leanamics"]["status"]
    if status not in LEAN_MARKS:
        sys.exit(f"{row['id']}: unknown leanamics status {status!r}")
    return LEAN_MARKS[status]


def check_ascii(s, where):
    bad = sorted({c for c in s if ord(c) > 127})
    if bad:
        sys.exit(f"non-ASCII characters {bad} in the LaTeX output ({where}); use LaTeX in `paper`")


def table(data):
    fields = field_keys(data)
    cols = "".join(
        r">{\raggedright\arraybackslash}p{%.2fcm}" % WIDTHS[k]
        for k in fields + ["relation", "lean"]
    )
    heads = {f["key"]: f["short"] for f in data["fields"]}
    out = [
        "% Generated by scripts/dictionary_tex.py from home_page/_data/dictionary.yml; do not edit.",
        "% Needs \\usepackage{booktabs,array,afterpage,pdflscape} (and amssymb for \\checkmark).",
        "% A landscape page of its own, after the page where this file is input.",
        r"\afterpage{%",
        r"\begin{landscape}",
        r"\begin{table}[p]",
        # 8.5/10pt for the table and its caption (\caption switches to \normalsize), thinner
        # spaces around the arrows of reactions, small gaps between groups.
        r"\def\normalsize{\fontsize{8.5}{10}\selectfont}\normalsize\centering",
        r"\setlength{\tabcolsep}{2.5pt}\setlength{\abovecaptionskip}{4pt}",
        r"\thickmuskip=3mu plus 2mu",
        r"\begin{tabular}{@{}" + cols + "@{}}",
        r"\toprule",
        " & ".join(heads[k] for k in fields) + r" & Relation & Lean \\",
        r"\midrule",
    ]
    groups = [g["key"] for g in data["groups"]]
    rows = [r for r in data["rows"] if r.get("paper", {}).get("include", True)]
    first = True
    for g in groups:
        members = [r for r in rows if r["group"] == g]
        if not members:
            continue
        if not first:
            out.append(r"\addlinespace[2pt]")
        first = False
        for r in members:
            cells = [cell(r, k) for k in fields]
            cells.append(r["paper"]["relation"])
            cells.append(lean_cell(r))
            line = " & ".join(cells) + r" \\"
            check_ascii(line, r["id"])
            out.append(line)
    caption = data["paper_caption"].strip()
    check_ascii(caption, "paper_caption")
    out += [
        r"\bottomrule",
        r"\end{tabular}",
        r"\caption{" + caption + "}",
        r"\label{tab:dictionary}",
        r"\end{table}",
        r"\end{landscape}}",
    ]
    return "\n".join(out) + "\n"


def cited_keys(data):
    keys = []
    for r in data["rows"]:
        if not r.get("paper", {}).get("include", True):
            continue
        for ks in r.get("paper", {}).get("cite", {}).values():
            for k in ks:
                if k not in keys:
                    keys.append(k)
    return keys


def bib_keys(path):
    return set(re.findall(r"@\w+\s*\{\s*([^,\s]+)\s*,", Path(path).read_text(encoding="utf-8")))


BIB_FIELDS = ["author", "title", "journal", "booktitle", "series", "volume", "number", "pages",
              "publisher", "address", "edition", "year", "doi", "eprint", "archiveprefix", "note"]


def bibtex(key, ref):
    if "bibtex" not in ref:
        sys.exit(f"reference {key} has no `bibtex` fields")
    b = dict(ref["bibtex"])
    kind = b.pop("type")
    lines = [f"@{kind}{{{key},"]
    for f in BIB_FIELDS:
        if f in b:
            lines.append(f"  {f:<13} = {{{b.pop(f)}}},")
    if b:
        sys.exit(f"reference {key}: unknown BibTeX fields {sorted(b)}")
    lines.append("}")
    return "\n".join(lines)


def blueprint_index():
    """Lean names tagged in the blueprints (checked by `checkdecls` in CI) and labels, per package."""
    names, labels = set(), {}
    for tex in ROOT.glob("*/blueprint/src/content.tex"):
        s = tex.read_text(encoding="utf-8")
        for m in re.finditer(r"\\lean\{([^}]*)\}", s):
            names.update(n.strip() for n in m.group(1).split(",") if n.strip())
        labels[tex.parts[-4]] = set(re.findall(r"\\label\{([^}]*)\}", s))
    return names, labels


DECLARATION = re.compile(
    r"\b(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([\w.'!?]+)")


def lean_declarations():
    """Dotted names written after a declaration keyword in the Lean sources of each package
    (a directory with a `lakefile.toml`), outside `.lake`."""
    decls = {}
    for lake in ROOT.glob("*/lakefile.toml"):
        pkg = lake.parent
        names = set()
        for f in pkg.rglob("*.lean"):
            if ".lake" not in f.relative_to(pkg).parts:
                names.update(DECLARATION.findall(f.read_text(encoding="utf-8")))
        decls[pkg.name] = names
    return decls


def is_declared(name, names):
    """Whether one of the declared dotted `names` ends the Lean name `name`, component by
    component."""
    parts = name.split(".")
    return any(".".join(parts[i:]) in names for i in range(len(parts)))


def roadmap_ids():
    """Target IDs of ROADMAP.md (first cell of its table rows, e.g. `| VOT-3 |`)."""
    text = (ROOT / "ROADMAP.md").read_text(encoding="utf-8")
    return set(re.findall(r"^\|\s*([A-Z]{3}-\d+)\s*\|", text, re.M))


def texts(obj):
    """All strings in a YAML value."""
    if isinstance(obj, str):
        yield obj
    elif isinstance(obj, dict):
        for v in obj.values():
            yield from texts(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from texts(v)


def check(data):
    """Consistency of the YAML with itself, the blueprints and the roadmap; returns a list of
    problems."""
    problems = []
    refs = data["references"]
    kinds = {r["key"] for r in data["relations"]}
    groups = {g["key"] for g in data["groups"]}
    fields = [f["key"] for f in data["fields"]]
    for f in fields:
        if f not in WIDTHS:
            problems.append(f"field {f} has no column width in scripts/dictionary_tex.py")
    names, labels = blueprint_index()
    decls = lean_declarations()
    targets = roadmap_ids()
    ids = [r["id"] for r in data["rows"]]
    if len(ids) != len(set(ids)):
        problems.append("duplicate row ids")
    for r in data["rows"]:
        rid = r["id"]
        if r["group"] not in groups:
            problems.append(f"{rid}: unknown group {r['group']}")
        for f in fields:
            c = r.get(f)
            if not isinstance(c, dict) or ("none" in c) == ("name" in c):
                problems.append(f"{rid}: field {f} needs either `name` or `none`")
                continue
            if "name" in c and not ("description" in c and "refs" in c):
                problems.append(f"{rid}: field {f} has a name but no description or refs")
            for k in c.get("refs", []):
                if k not in refs:
                    problems.append(f"{rid}.{f}: unknown reference {k}")
        for k in r["relation"]["kinds"]:
            if k not in kinds:
                problems.append(f"{rid}: unknown relation kind {k}")
        for k in r["relation"].get("refs", []):
            if k not in refs:
                problems.append(f"{rid}.relation: unknown reference {k}")
        for key in fields + ["relation"]:
            for s in texts(r.get(key)):
                if s.count("$") % 2:
                    problems.append(f"{rid}.{key}: unbalanced $ in {s[:50]!r}")
                if s.count("`") % 2:
                    problems.append(f"{rid}.{key}: unbalanced backtick in {s[:50]!r}")
        lean = r["leanamics"]
        if lean["status"] not in LEAN_MARKS:
            problems.append(f"{rid}: unknown status {lean['status']}")
        if lean["status"] == "not-formalized" and any(lean.get(k) for k in LEAN_LISTS):
            problems.append(f"{rid}: status not-formalized, but Lean material is listed")
        for n in lean.get("correspondence", []) + lean.get("results", []):
            if n not in names:
                problems.append(f"{rid}: Lean name {n} is not tagged in any blueprint")
            if not any(is_declared(n, decls.get(p, set())) for p in lean.get("packages", [])):
                problems.append(f"{rid}: Lean name {n} is not declared in the sources of the "
                                f"row's packages {lean.get('packages', [])}")
        for url in lean.get("blueprint", []):
            m = re.fullmatch(r"/([\w-]+)/blueprint/(?:#(.+))?", url)
            if not m or m.group(1) not in labels:
                problems.append(f"{rid}: malformed blueprint link {url}")
            elif m.group(2) and m.group(2) not in labels[m.group(1)]:
                problems.append(f"{rid}: no label {m.group(2)} in {m.group(1)}/blueprint")
        for t in lean.get("roadmap", []):
            if t not in targets:
                problems.append(f"{rid}: roadmap target {t} is not in ROADMAP.md")
        for p in lean.get("packages", []):
            if p not in labels:
                problems.append(f"{rid}: unknown package {p}")
        paper = r.get("paper", {})
        if paper.get("include", True):
            for key in fields + ["relation"]:
                if key not in paper:
                    problems.append(f"{rid}.paper: no {key}")
                elif any(ord(ch) > 127 for ch in paper[key]):
                    problems.append(f"{rid}.paper.{key}: non-ASCII characters (use LaTeX)")
        for f, ks in paper.get("cite", {}).items():
            if f not in fields:
                problems.append(f"{rid}.paper.cite: unknown field {f}")
            for key in ks:
                if key not in refs:
                    problems.append(f"{rid}.paper: unknown reference {key}")
                elif not refs[key].get("in_paper_bib") and "bibtex" not in refs[key]:
                    problems.append(f"{rid}.paper: reference {key} has no `bibtex` fields")
    used = set()
    for r in data["rows"]:
        for f in fields:
            if isinstance(r.get(f), dict):
                used.update(r[f].get("refs", []))
        used.update(r["relation"].get("refs", []))
        for ks in r.get("paper", {}).get("cite", {}).values():
            used.update(ks)
    for k, ref in refs.items():
        if not (ref.get("doi") or ref.get("arxiv") or ref.get("isbn") or ref.get("no_identifier")):
            problems.append(f"reference {k}: no DOI, arXiv id or ISBN")
        if k not in used:
            problems.append(f"reference {k} is not cited by any row")
        b = ref.get("bibtex")
        if b:
            extra = set(b) - set(BIB_FIELDS) - {"type"}
            if "type" not in b or extra:
                problems.append(f"reference {k}: no BibTeX type or unknown fields {sorted(extra)}")
            if ref.get("doi") and b.get("doi") != ref["doi"]:
                problems.append(f"reference {k}: BibTeX doi differs from its doi")
    text = Path(data["_path"]).read_text(encoding="utf-8")
    if "\u2014" in text:
        problems.append("em dash in the YAML")
    return problems


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--data", default=str(DATA), help="dictionary YAML (default: %(default)s)")
    ap.add_argument("--table", help="write the LaTeX table here instead of stdout")
    ap.add_argument("--bib", help="write BibTeX entries of cited keys not in the paper's bibliography")
    ap.add_argument("--check-bib", help="the paper's .bib file, to check the keys marked in_paper_bib")
    ap.add_argument("--check", action="store_true",
                    help="only check the YAML (cells of every field, references, relation kinds, "
                         "Lean names against the blueprints' \\lean tags and the declarations of "
                         "the row's packages, blueprint links against their \\label's, roadmap "
                         "IDs)")
    args = ap.parse_args()

    data = load(args.data)
    data["_path"] = args.data
    if args.check:
        problems = check(data)
        for p in problems:
            print(p, file=sys.stderr)
        n = len(data["rows"])
        print(f"{n} rows, {len(data['fields'])} fields, {len(data['references'])} references: "
              + ("ok" if not problems else f"{len(problems)} problems"), file=sys.stderr)
        sys.exit(1 if problems else 0)
    refs = data["references"]
    keys = cited_keys(data)
    for k in keys:
        if k not in refs:
            sys.exit(f"cited key {k} is not in `references`")
    have = set()
    if args.check_bib:
        have = bib_keys(args.check_bib)
        for k, ref in refs.items():
            if ref.get("in_paper_bib") and k not in have:
                sys.exit(f"{k} is marked in_paper_bib but is not in {args.check_bib}")
        new = [k for k in keys if k not in have]
        print("cited keys not in the paper's bibliography: " + (", ".join(new) or "none"),
              file=sys.stderr)

    tex = table(data)
    if args.table:
        Path(args.table).write_text(tex, encoding="utf-8")
    else:
        sys.stdout.write(tex)

    if args.bib:
        new = [k for k in keys if not refs[k].get("in_paper_bib") and k not in have]
        entries = [bibtex(k, refs[k]) for k in new]
        header = ("% BibTeX entries cited by the dictionary table and not in the paper's "
                  "bibliography.\n% Generated by scripts/dictionary_tex.py from "
                  "home_page/_data/dictionary.yml.\n\n")
        Path(args.bib).write_text(header + "\n\n".join(entries) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
