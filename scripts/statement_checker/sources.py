"""Where an item comes from: the source data file, PROVENANCE.md and the package READMEs.

`verification/sources.toml` (optional) gives, per item, the source reference and, when
available, the original statement transcribed from the source. The Markdown tables of
PROVENANCE.md and of the package READMEs are matched to items through the Lean names they cite.
"""
import fnmatch
import re
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

SOURCE_FIELDS = {"item", "items", "paper", "venue", "version", "result", "page", "url",
                 "status", "statement", "context", "notes"}
REQUIRED_FIELDS = {"paper", "result", "status"}
TICKS = re.compile(r"`([^`]+)`")
LEANISH = re.compile(r"^[A-Za-z_][\w'.!?*/]*$")


@dataclass
class TableRow:
    file: str           # repository-relative path
    line: int
    heading: str        # the Markdown heading above the table
    header: list        # column titles
    cells: list         # cell texts (Markdown)
    names: list = field(default_factory=list)   # candidate full names / patterns
    package: str = ""

    def text(self, skip=()):
        out = []
        for h, c in zip(self.header, self.cells):
            if h in skip or not c.strip():
                continue
            out.append(f"{h}: {c}")
        return "\n".join(out)


def split_row(line):
    """The cells of a Markdown table row (escaped pipes `\\|` stay inside cells)."""
    parts = re.split(r"(?<!\\)\|", line.strip())
    if parts and parts[0] == "":
        parts = parts[1:]
    if parts and parts[-1] == "":
        parts = parts[:-1]
    return [p.strip().replace("\\|", "|") for p in parts]


def tables(path, rel):
    """All rows of all Markdown tables of a file, with their header and heading."""
    rows, heading, header = [], "", None
    lines = Path(path).read_text(encoding="utf-8").split("\n")
    for k, line in enumerate(lines):
        if line.startswith("#"):
            heading = line.lstrip("#").strip()
            header = None
            continue
        if not line.startswith("|"):
            header = None
            continue
        cells = split_row(line)
        if header is None:
            header = cells
            continue
        if all(re.fullmatch(r":?-+:?", c) for c in cells if c):
            continue
        rows.append(TableRow(rel, k + 1, heading, header, cells))
    return rows


def expand_token(tok):
    """`lemma_3_1_a/b/c` -> lemma_3_1_a, lemma_3_1_b, lemma_3_1_c; other tokens unchanged."""
    m = re.fullmatch(r"(.*_)([^_/]+)((?:/[^_/]+)+)", tok)
    if m:
        return [m.group(1) + x for x in [m.group(2)] + m.group(3).split("/")[1:]]
    return [tok]


def lean_tokens(cell):
    out = []
    for t in TICKS.findall(cell):
        t = t.strip()
        if " " in t or not LEANISH.match(t) or t.endswith(".lean"):
            continue
        out += expand_token(t)
    return out


def _namespaced_candidates(tokens):
    """Full-name candidates for the tokens of one cell: the names after a qualified name are
    in its namespace (the convention of RESULTS.md and PROVENANCE.md)."""
    cands, ns = [], ""
    for t in tokens:
        cands.append(t)
        if "." in t and t[0].isupper():
            ns = t.rsplit(".", 1)[0]
            parts = ns.split(".")
            for k in range(1, len(parts) + 1):
                cands.append(".".join(parts[:k]) + "." + t)
        elif ns:
            parts = ns.split(".")
            for k in range(len(parts), 0, -1):
                cands.append(".".join(parts[:k]) + "." + t)
    return cands


def provenance_rows(root):
    """Rows of the result tables of PROVENANCE.md and of its table of explicit constants."""
    path = Path(root) / "PROVENANCE.md"
    if not path.is_file():
        return []
    rows = tables(path, "PROVENANCE.md")
    for r in rows:
        r.names = _namespaced_candidates(lean_tokens(r.cells[0])) if r.cells else []
        m = re.search(r"\(`(\w+)/`", r.heading)
        r.package = m.group(1) if m else ""
    return rows


def readme_rows(root, packages):
    rows = []
    for pkg in packages:
        path = Path(root) / pkg / "README.md"
        if not path.is_file():
            continue
        for r in tables(path, f"{pkg}/README.md"):
            r.package = pkg
            toks = [t for c in r.cells for t in lean_tokens(c)]
            r.names = toks
            if toks:
                rows.append(r)
    return rows


def row_matches(row, full_name, by_suffix):
    """Whether a table row cites the Lean declaration `full_name`."""
    for c in row.names:
        if "*" in c:
            if fnmatch.fnmatchcase(full_name, c) or fnmatch.fnmatchcase(full_name, "*." + c):
                return True
        elif c == full_name:
            return True
        elif by_suffix and full_name.endswith("." + c):
            return True
    return False


LINK_PATTERNS = [
    (re.compile(r"arXiv[:\s]*(\d{4}\.\d{4,5})(v\d+)?", re.I), "https://arxiv.org/abs/{0}{1}"),
    (re.compile(r"arxiv\.org/(?:abs|pdf)/(\d{4}\.\d{4,5})(v\d+)?"), "https://arxiv.org/abs/{0}{1}"),
    (re.compile(r"(?:doi[:\s]*|doi\.org/|DOI:\s*)(10\.\d{4,9}/[^\s)\],;`]+)", re.I),
     "https://doi.org/{0}"),
]


def links(text):
    """arXiv and DOI links mentioned in a text, in order, without duplicates."""
    out = []
    for pat, fmt in LINK_PATTERNS:
        for m in pat.finditer(text):
            url = fmt.format(*[g or "" for g in m.groups()]).rstrip(".")
            if url not in out:
                out.append(url)
    return out


def load_sources(path):
    """The entries of the sources file, as a list of dicts with an `items` list.

    Returns (entries, problems)."""
    path = Path(path)
    if not path.is_file():
        return [], []
    problems = []
    try:
        with open(path, "rb") as f:
            data = tomllib.load(f)
    except tomllib.TOMLDecodeError as e:
        return [], [f"{path.name}: {e}"]
    entries = []
    for k, e in enumerate(data.get("source", [])):
        where = f"{path.name}: entry {k + 1}"
        unknown = set(e) - SOURCE_FIELDS
        if unknown:
            problems.append(f"{where}: unknown fields {sorted(unknown)}")
        ids = ([e["item"]] if isinstance(e.get("item"), str) else []) + list(e.get("items", []))
        if not ids:
            problems.append(f"{where}: no `item`")
        missing = REQUIRED_FIELDS - set(e)
        if missing:
            problems.append(f"{where} ({', '.join(ids)}): missing {sorted(missing)}")
        e = dict(e)
        e["items"] = ids
        for key in ("statement", "context"):
            if key in e:
                e[key] = e[key].strip("\n")
        entries.append(e)
    extra = set(data) - {"source"}
    if extra:
        problems.append(f"{path.name}: unknown top-level keys {sorted(extra)}")
    return entries, problems
