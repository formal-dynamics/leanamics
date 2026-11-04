"""The items to check, with everything the reviewer needs, their hashes and their status."""
import glob
import json
import os
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from . import blueprint, checks, lean_decls, sources

# The order of the packages in the paper (as in scripts/library_sizes.py).
PACKAGE_ORDER = ["dynamics", "voter", "moran", "plurality", "median", "undecided", "averaging",
                 "epidemics", "crn"]
SOURCES_FILE = "verification/sources.toml"
CHECKS_DIR = "verification/checks"
TIERS = {0: "main result", 1: "definition used by a main result", 2: "result in PROVENANCE.md",
         3: "definition", 4: "other"}


@dataclass
class Entry:
    """One item of the blueprint, enriched."""
    item: blueprint.Item
    decls: list                     # (name, Decl or None)
    used: list = field(default_factory=list)       # library names used by the statement
    provenance: list = field(default_factory=list)  # TableRow
    readme: list = field(default_factory=list)      # TableRow
    sources: list = field(default_factory=list)     # entries of sources.toml
    lean_hash: str = ""
    source_hash: str = ""
    tier: int = 4
    order: int = 0

    @property
    def id(self):
        return self.item.id

    @property
    def missing(self):
        return [n for n, d in self.decls if d is None]

    @property
    def is_definition(self):
        return self.item.env == "definition"

    @property
    def kind(self):
        return {"definition": "def", "theorem": "thm", "lemma": "lem", "corollary": "cor",
                "proposition": "prop", "remark": "rmk"}.get(self.item.env, self.item.env[:4])

    def links(self):
        out = []
        for s in self.sources:
            for u in [s.get("url", "")] + sources.links(s.get("version", "")):
                if u and u not in out:
                    out.append(u)
        texts = [r.text() for r in self.provenance + self.readme] + [self.item.statement, self.item.title,
                                                      self.item.section_intro]
        for t in texts:
            for u in sources.links(t):
                if u not in out:
                    out.append(u)
        for m in re.finditer(r"\\href\{([^}]*)\}", self.item.statement + self.item.section_intro):
            if m.group(1) not in out:
                out.append(m.group(1))
        return out

    def search_text(self):
        return "\n".join([self.id, self.item.title, self.item.statement, self.item.section,
                          " ".join(self.item.lean)]).lower()


def lean_hash_text(entry):
    parts = []
    for name, d in entry.decls:
        parts.append(name)
        parts.append(d.check_text() if d else "<missing>")
    return "\n\n".join(parts)


def source_hash_text(entry):
    """The text whose hash identifies the source side: the blueprint title and statement and
    the transcribed original statements (whitespace collapsed)."""
    norm = lambda s: " ".join(str(s).split())
    parts = [norm(entry.item.title), norm(entry.item.statement)]
    for s in entry.sources:
        parts += [norm(s.get(k, "")) for k in ("version", "result", "statement", "context")]
    return "\n".join(parts)


def _cache_path():
    base = os.environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache")
    return Path(base) / "leanamics-statement-checker" / "mathlib-names.json"


def _cache_load():
    try:
        return json.loads(_cache_path().read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def _cache_save(cache):
    try:
        p = _cache_path()
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(cache, indent=0, sort_keys=True), encoding="utf-8")
    except OSError:
        pass


class Model:
    def __init__(self, root, checks_dir=None, sources_file=None, reviewer=None):
        self.root = Path(root)
        self.reviewer = reviewer
        self.index = lean_decls.build_index(self.root)
        self.external = {}          # names found outside the library (Mathlib)
        self.items = []
        self.abstracts = {}
        for pkg in self.packages():
            path = self.root / pkg / "blueprint" / "src" / "content.tex"
            tex = path.read_text(encoding="utf-8")
            self.abstracts[pkg] = blueprint.abstract(tex)
            self.items += blueprint.parse(tex, pkg, str(path.relative_to(self.root)))
        self.prov_rows = sources.provenance_rows(self.root)
        self.readme_rows = sources.readme_rows(self.root, self.packages())
        self.sources_path = self.root / (sources_file or SOURCES_FILE)
        self.source_entries, self.source_problems = sources.load_sources(self.sources_path)
        self.entries = [self._entry(it) for it in self.items]
        self.by_id = {e.id: e for e in self.entries}
        self.by_decl = {}
        for e in self.entries:
            for n in e.item.lean:
                self.by_decl.setdefault(n, []).append(e)
        self._prioritize()
        self.store = checks.Store(self.root / (checks_dir or CHECKS_DIR)
                                  if checks_dir is None or not Path(checks_dir).is_absolute()
                                  else checks_dir)

    def packages(self):
        have = {Path(p).parts[-4] for p in glob.glob(str(self.root / "*/blueprint/src/content.tex"))}
        return [p for p in PACKAGE_ORDER if p in have] + sorted(have - set(PACKAGE_ORDER))

    def _entry(self, it):
        decls = []
        for n in it.lean:
            d = self.index.get(n)
            if d is None:
                d = self.external_decl(n)
            decls.append((n, d))
        e = Entry(item=it, decls=decls)
        used = []
        for n, d in decls:
            if d is None or d.package == "mathlib":
                continue
            for r in self.index.refs(d):
                if r not in it.lean and r not in used:
                    used.append(r)
        e.used = used
        e.provenance = [r for r in self.prov_rows
                        if any(sources.row_matches(r, n, False) for n in it.lean)]
        e.readme = [r for r in self.readme_rows if r.package == it.package and
                    any(sources.row_matches(r, n, True) for n in it.lean)]
        e.sources = [s for s in self.source_entries if it.id in s["items"]]
        e.lean_hash = checks.digest(lean_hash_text(e))
        e.source_hash = checks.digest(source_hash_text(e))
        return e

    def external_decl(self, name):
        """A declaration of Mathlib (searched in the `.lake` of a package), or None."""
        if name in self.external:
            return self.external[name]
        found = None
        roots = sorted(glob.glob(str(self.root / "*/.lake/packages/mathlib/Mathlib")))
        last = name.rsplit(".", 1)[-1]
        cache = _cache_load()
        hit = cache.get(name)
        if roots and hit and Path(roots[0], hit).is_file():
            for d in lean_decls.parse_file(Path(roots[0], hit).read_text(encoding="utf-8"),
                                           "mathlib", "Mathlib/" + hit):
                if d.name == name:
                    self.external[name] = d
                    return d
        if roots and re.fullmatch(r"[\w'.!?]+", name):
            try:
                out = subprocess.run(
                    ["grep", "-rlE", "--include=*.lean",
                     r"^(@\[.*\] *)?((private|protected|noncomputable) +)*"
                     r"(theorem|lemma|def|abbrev|structure|class|instance) +([\w.']*\.)?"
                     + re.escape(last) + r"( |$)", roots[0]],
                    capture_output=True, text=True, timeout=60).stdout.split()
            except (OSError, subprocess.TimeoutExpired):
                out = []
            for path in out:
                for d in lean_decls.parse_file(Path(path).read_text(encoding="utf-8"),
                                               "mathlib", "Mathlib/" + path.split("/Mathlib/", 1)[-1]):
                    if d.name == name:
                        found = d
                        cache[name] = path.split("/Mathlib/", 1)[-1]
                        _cache_save(cache)
                        break
                if found:
                    break
        self.external[name] = found
        return found

    def _prioritize(self):
        """Tiers: main results, definitions they use, other PROVENANCE results, definitions,
        the rest; within a tier, the package order of the paper and the blueprint order."""
        first_names = set()
        for r in self.prov_rows:
            if r.package == "dynamics":  # the shared layer: standard results, not case studies
                continue
            if r.heading.startswith("Explicit constants") or (r.header and r.header[0] == "Result"
                                                                and r.names):
                toks = sources.lean_tokens(r.cells[0])
                if toks:
                    first_names.update(sources._namespaced_candidates(toks[:1]))
        main = set()
        for e in self.entries:
            if e.sources or any(n in first_names for n in e.item.lean):
                main.add(e.id)
            elif any(sources.row_matches(r, n, False) for r in self.prov_rows
                     if r.heading.startswith("Explicit constants") for n in e.item.lean):
                main.add(e.id)
        # definitions used by the main results, transitively through the Lean statements
        defs_of_main = set()
        todo = [n for e in self.entries if e.id in main for n in e.used]
        seen = set()
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            seen.add(n)
            d = self.index.get(n)
            if d is None or not d.is_definition:
                continue
            for e in self.by_decl.get(n, []):
                if e.id not in main:
                    defs_of_main.add(e.id)
            todo += self.index.refs(d)
        pkg_rank = {p: k for k, p in enumerate(self.packages())}
        for k, e in enumerate(self.entries):
            if e.id in main:
                e.tier = 0
            elif e.id in defs_of_main:
                e.tier = 1
            elif e.provenance:
                e.tier = 2
            elif e.is_definition:
                e.tier = 3
            else:
                e.tier = 4
            e.order = k
        self.priority = sorted(self.entries, key=lambda e: (e.tier, pkg_rank.get(e.item.package, 99), e.order))

    def item_for_decl(self, name, package=None):
        """An item naming the declaration, preferably one of the given package."""
        hits = self.by_decl.get(name, [])
        same = [e for e in hits if e.item.package == package]
        return (same or hits or [None])[0]

    def status(self, entry):
        return checks.status(self.store.for_item(entry.id), entry.lean_hash, entry.source_hash,
                             self.reviewer)

    def record(self, entry, verdict, comment):
        if verdict not in checks.VERDICTS:
            raise ValueError(f"unknown verdict {verdict}")
        if verdict in checks.NEEDS_COMMENT and not comment.strip():
            raise ValueError(f"`{verdict}` needs a comment")
        if not self.reviewer:
            raise ValueError("no reviewer name (use --reviewer or git config user.name)")
        c = checks.Check(item=entry.id, reviewer=self.reviewer, date=checks.now(),
                         verdict=verdict, comment=comment.strip(), lean_hash=entry.lean_hash,
                         source_hash=entry.source_hash, lean=tuple(entry.item.lean))
        self.store.append(c)
        return c

    def defined_used_not_items(self):
        """Library definitions used by statements of items that are not themselves items."""
        out = {}
        for e in self.entries:
            for n in e.used:
                d = self.index.get(n)
                if d is not None and d.is_definition and n not in self.by_decl:
                    if d.parent and d.parent in self.by_decl:
                        continue
                    out.setdefault(n, []).append(e.id)
        return out
