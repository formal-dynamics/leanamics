"""Extract declarations from the Lean sources of the repository, by reading the text.

This is not a Lean parser. It relies on the conventions of the library, which the tests check
over the whole repository: every command starts in column 0 (after its doc comment and
attributes), and namespaces are opened with `namespace` and closed with `end`. For each
declaration it records the fully qualified name, the kind, the file and line, the doc comment,
the text of the declaration, its statement (the signature up to the top-level `:=` for theorems
and instances, the whole text for definitions), the section `variable`s the statement uses, and
the identifiers of the statement, resolved against the other declarations of the library.
"""
import bisect
import os
import re
from dataclasses import dataclass, field
from pathlib import Path

DEF_KINDS = {"def", "abbrev", "structure", "class", "inductive", "opaque", "irreducible_def",
             "axiom", "class inductive"}
THM_KINDS = {"theorem", "lemma", "instance", "alias"}
MODIFIERS = ("private", "protected", "public", "noncomputable", "nonrec", "partial", "unsafe",
             "local", "scoped", "meta")
DECL_KW = ("theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
           "opaque", "irreducible_def", "axiom", "example", "alias")
OTHER_KW = ("namespace", "section", "end", "variable", "open", "include", "omit", "universe",
            "set_option", "mutual", "attribute", "export", "notation", "infix", "infixl",
            "infixr", "prefix", "postfix", "macro", "macro_rules", "syntax", "elab", "deriving",
            "initialize", "import", "module", "local", "scoped", "add_decl_doc", "assert_not_exists",
            "suppress_compilation", "noncomputable", "unseal", "seal", "compile_inductive",
            "register_option", "declare_syntax_cat", "run_cmd", "lemma")
CMD_START = re.compile(
    r"^(?:@\[|#[a-z_]+|(?:" + "|".join(DECL_KW + OTHER_KW + MODIFIERS) + r")(?![\w'!?.]))", re.M)
ATTRS = re.compile(r"@\[(?:[^\[\]]|\[[^\]]*\])*\]\s*")
HEAD = re.compile(
    r"^(?P<prefix>(?:@\[(?:[^\[\]]|\[[^\]]*\])*\]\s*)*(?:(?:" + "|".join(MODIFIERS) +
    r")\s+)*)(?P<kw>class\s+inductive|" + "|".join(DECL_KW) + r")(?![\w'!?.])")
IDENT = re.compile(r"(?<![\w'!?.₀-₉₀-ₜ])(?:[^\W\d]|_)[\w'!?₀-₉₀-ₜ]*"
                   r"(?:\.(?:[^\W\d]|_)[\w'!?₀-₉₀-ₜ]*)*", re.U)
NAME = re.compile(r"«[^»]*»|(?:[^\W\d]|_)[\w'!?₀-₉₀-ₜ]*(?:\.(?:«[^»]*»|(?:[^\W\d]|_)"
                  r"[\w'!?₀-₉₀-ₜ]*))*", re.U)
_N = "(?:" + NAME.pattern + ")"
OPEN_BR = "([{⟨⦃⟪⁅"
CLOSE_BR = ")]}⟩⦄⟫⁆"
LEAN_KEYWORDS = {
    "fun", "λ", "let", "have", "show", "from", "by", "at", "if", "then", "else", "do", "match",
    "with", "in", "Type", "Sort", "Prop", "forall", "exists", "where", "this", "true", "false",
    "True", "False", "deriving", "extends", "calc", "open", "for", "return", "mut", "_"}


@dataclass
class Decl:
    name: str              # fully qualified
    kind: str              # theorem, lemma, def, abbrev, structure, field, constructor, ...
    package: str
    path: str              # repository-relative
    line: int              # 1-based line of the keyword
    doc: str               # doc comment (without /-- -/), or ""
    text: str              # the declaration as written (attributes, keyword, ..., end)
    statement: str         # what must be checked: signature up to := for theorems, else text
    variables: list = field(default_factory=list)   # section variable binders it uses
    namespace: str = ""
    opens: list = field(default_factory=list)
    parent: str = ""       # for fields and constructors: the structure/inductive
    private: bool = False

    @property
    def is_definition(self):
        return self.kind in DEF_KINDS or self.kind in ("field", "constructor")

    def check_text(self):
        """The text whose hash identifies the statement: code without comments, whitespace
        collapsed, with the section variables it uses."""
        parts = [" ".join(mask(self.statement).split())]
        parts += [" ".join(v.split()) for v in self.variables]
        return "\n".join(parts)


_NEST = re.compile(r"/-|-/")


def _comment_end(text, k):
    """Offset after the block comment whose body starts at k (after its opening `/-`)."""
    depth = 1
    while depth:
        m = _NEST.search(text, k)
        if not m:
            return len(text)
        depth += 1 if m.group() == "/-" else -1
        k = m.end()
    return k


def mask(text, keep_doc=False):
    """Replace comments (and string contents) by spaces, keeping offsets and line breaks."""
    out, i, n = [], 0, len(text)
    pat = re.compile(r'--|/-|"')
    while i < n:
        m = pat.search(text, i)
        if not m:
            out.append(text[i:])
            break
        j = m.start()
        out.append(text[i:j])
        tok = m.group()
        if tok == "--":
            k = text.find("\n", j)
            k = n if k < 0 else k
            out.append(" " * (k - j))
            i = k
        elif tok == "/-":
            k = _comment_end(text, j + 2)
            out.append(re.sub(r"[^\n]", " ", text[j:k]))
            i = k
        else:  # string literal
            k = j + 1
            while k < n and text[k] != '"':
                k += 2 if text[k] == "\\" else 1
            out.append('"' + re.sub(r"[^\n]", " ", text[j + 1:k]) + '"')
            i = k + 1
    return "".join(out)


def doc_comments(text):
    """Spans (start, end, content) of the doc comments `/-- ... -/` of a file."""
    spans = []
    for m in re.finditer(r"/--", text):
        # skip occurrences inside an earlier span
        if spans and m.start() < spans[-1][1]:
            continue
        k = _comment_end(text, m.end())
        spans.append((m.start(), k, text[m.end():k - 2].strip()))
    return spans


def _scan_to(masked, start, stop_at_bar=False):
    """Offset of the first top-level `:=` (or ` where`, or a line starting with `|` when
    stop_at_bar) at or after start; None if there is none."""
    depth, i, n = 0, start, len(masked)
    while i < n:
        c = masked[i]
        if c in OPEN_BR:
            depth += 1
        elif c in CLOSE_BR:
            depth = max(0, depth - 1)
        elif depth == 0:
            if c == ":" and i + 1 < n and masked[i + 1] == "=":
                return i
            if c == "\n" and stop_at_bar:
                m = re.match(r"\n\s*\|", masked[i:])
                if m:
                    return i
            if c == "w" and masked.startswith("where", i) and (i == 0 or not
                                                                (masked[i - 1].isalnum() or masked[i - 1] in "_'.")) \
                    and (i + 5 >= n or not (masked[i + 5].isalnum() or masked[i + 5] in "_'")):
                return i
        i += 1
    return None


def _binders(var_text):
    """Split the binder groups of a `variable` command: list of (text, names, kind)."""
    groups, i, n = [], 0, len(var_text)
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "{{": "}}"}
    while i < n:
        c = var_text[i]
        if c in "({[⦃":
            close = pairs[c]
            depth, j = 0, i
            while j < n:
                if var_text[j] in "({[⦃⟨":
                    depth += 1
                elif var_text[j] in ")}]⦄⟩":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            inner = var_text[i + 1:j]
            grp = var_text[i:j + 1]
            names = []
            if ":" in inner and c != "[":
                head = inner.split(":", 1)[0]
                names = [t for t in head.split() if NAME.fullmatch(t)]
            elif c == "[" and ":" in inner.split("]")[0]:
                head = inner.split(":", 1)[0].strip()
                if NAME.fullmatch(head):
                    names = [head]
            groups.append((grp, names, c, inner))
            i = j + 1
        else:
            i += 1
    return groups


def _idents(text):
    return set(IDENT.findall(text))


def _top_colon(text):
    """Offset of the first `:` at bracket depth 0 that is not part of `:=`, or None."""
    depth = 0
    for i, c in enumerate(text):
        if c in OPEN_BR:
            depth += 1
        elif c in CLOSE_BR:
            depth = max(0, depth - 1)
        elif c == ":" and depth == 0 and text[i + 1:i + 2] != "=":
            return i
    return None


_BINDER_GROUP = re.compile(r"[(\{⦃\[]\s*([^():{}\[\]⦃⦄]*?)\s*:(?!=)")
_QUANT = re.compile(r"(?:∀|∃!?|fun|λ|∑|∏|⋃|⋂|⨆|⨅|let|Π|Σ)\s+((?:[^,=↦]|=(?!>))*?)\s*(?:,|=>|↦|:=)")


def _bound_names(masked_sig):
    """Names bound by a signature: the binders before its top-level colon, and the variables
    of ∀, ∃, fun, ∑, ... (with or without binder groups)."""
    names = set()
    colon = _top_colon(masked_sig)
    header = masked_sig if colon is None else masked_sig[:colon]
    for m in _BINDER_GROUP.finditer(header):
        names.update(t for t in m.group(1).split() if NAME.fullmatch(t))
    for m in _QUANT.finditer(masked_sig):
        binders = m.group(1)
        groups = _BINDER_GROUP.findall(binders)
        if groups:
            for g in groups:
                names.update(t for t in g.split() if NAME.fullmatch(t))
        else:
            head = re.split(r"[:∈∉<≤>≥⊆]|\bin\b", binders)[0]
            names.update(t.strip("(){}[]⦃⦄") for t in head.split() if NAME.fullmatch(t.strip("(){}[]⦃⦄")))
    return names


def _relevant_variables(scopes_vars, masked_sig, omitted, included):
    """The binders of the section variables that the statement uses (closure of the names it
    mentions, then the instance binders all of whose variables are used)."""
    groups = []
    for v in scopes_vars:
        body = re.sub(r"^\s*variable\s*", "", v)
        groups += _binders(body)
    norm = lambda s: " ".join(s.split())
    omitted_n = {norm(o) for o in omitted}
    groups = [g for g in groups if norm(g[0]) not in omitted_n
              and not (g[1] and any(nm in omitted for nm in g[1]))]
    all_vars = {nm for g in groups for nm in g[1]}
    used = (_idents(masked_sig) - _bound_names(masked_sig)) | set(included)
    used = {u.split(".")[0] for u in used} | used
    keep = set()
    changed = True
    while changed:
        changed = False
        for k, g in enumerate(groups):
            if k in keep or not g[1]:
                continue
            if any(nm in used for nm in g[1]):
                keep.add(k)
                new = {u.split(".")[0] for u in _idents(g[3].split(":", 1)[-1])}
                used |= new
                changed = True
    for k, g in enumerate(groups):
        if k in keep or g[1]:
            continue
        mentioned = {u.split(".")[0] for u in _idents(g[3])} & all_vars
        if mentioned and mentioned <= used:
            keep.add(k)
    out = []
    for k in sorted(keep):
        grp, names, opener, inner = groups[k]
        if len(names) > 1 and opener in "({⦃":
            mine = [nm for nm in names if nm in used]
            if mine and len(mine) < len(names):
                typ = inner.split(":", 1)[1].strip()
                grp = opener + " ".join(mine) + " : " + typ + grp[-1]
        out.append(grp)
    return out


@dataclass
class _Scope:
    kind: str      # namespace, section, mutual
    name: str
    variables: list = field(default_factory=list)
    opens: list = field(default_factory=list)
    included: list = field(default_factory=list)


def parse_file(text, package, path):
    """The declarations of one Lean file."""
    masked = mask(text)
    docs = doc_comments(text)
    lines_masked = masked.split("\n")
    # offsets of line starts
    offs = [0]
    for ln in lines_masked:
        offs.append(offs[-1] + len(ln) + 1)
    starts = [m.start() for m in CMD_START.finditer(masked)]
    starts_set = set(starts)
    doc_starts = {s for (s, _, _) in docs if s == 0 or text[s - 1] == "\n"}
    bounds = sorted(starts_set | doc_starts | {len(masked)})
    doc_by_end = {}
    for (s, e, content) in docs:
        doc_by_end[e] = (s, content)
    scopes = [_Scope("root", "")]
    decls = []
    prefix_omit, prefix_open, prefix_include = [], [], []

    def ns():
        return ".".join(s.name for s in scopes if s.kind == "namespace" and s.name)

    def line_of(off):
        return bisect.bisect_right(offs, off)

    for bi, b in enumerate(bounds[:-1]):
        if b in doc_starts and b not in starts_set:
            continue
        end = bounds[bi + 1]
        chunk_m = masked[b:end]
        chunk = text[b:end]
        # trim trailing blank (masked) lines
        lines_c = chunk_m.split("\n")
        while len(lines_c) > 1 and not lines_c[-1].strip():
            lines_c.pop()
        chunk_m = "\n".join(lines_c).rstrip()
        chunk = chunk[:len(chunk_m)]
        first = chunk_m.split(None, 1)[0] if chunk_m.split() else ""
        stripped_first = ATTRS.sub("", chunk_m).lstrip()
        word = re.match(r"[#\w]+", stripped_first)
        word = word.group() if word else ""
        if word == "namespace":
            nm = stripped_first.split()[1]
            scopes.append(_Scope("namespace", nm))
            continue
        if word in ("section",) or (word == "noncomputable" and re.match(r"noncomputable\s+section\b", stripped_first)):
            parts = stripped_first.split()
            nm = parts[2] if word == "noncomputable" and len(parts) > 2 else (
                parts[1] if word == "section" and len(parts) > 1 else "")
            scopes.append(_Scope("section", nm))
            continue
        if word == "mutual":
            scopes.append(_Scope("mutual", ""))
            continue
        if word == "end":
            if len(scopes) > 1:
                scopes.pop()
            continue
        is_prefix = re.search(r"\sin\s*$", chunk_m) is not None and word in (
            "omit", "open", "include", "set_option", "variable")
        if word == "variable":
            if is_prefix:
                scopes[-1].variables.append(chunk_m[:chunk_m.rfind(" in")])  # approximate
            else:
                scopes[-1].variables.append(chunk_m)
            continue
        if word == "omit":
            body = re.sub(r"^\s*omit\s*", "", chunk_m)
            body = re.sub(r"\s+in\s*$", "", body)
            items = [g[0] for g in _binders(body)] + [t for t in re.sub(r"[\[\(\{].*?[\]\)\}]", " ", body).split()]
            prefix_omit += items
            continue
        if word == "include":
            body = re.sub(r"^\s*include\s*", "", chunk_m)
            nm = re.sub(r"\s+in\s*$", "", body).split()
            if is_prefix:
                prefix_include += nm
            else:
                scopes[-1].included += nm
            continue
        if word == "open":
            body = re.sub(r"^\s*open\s+(scoped\s+)?", "", chunk_m)
            body = re.sub(r"\s+in\s*$", "", body)
            body = re.sub(r"\(.*?\)|hiding.*|renaming.*", " ", body)
            nms = [t for t in body.split() if NAME.fullmatch(t)]
            if is_prefix:
                prefix_open += nms
            else:
                scopes[-1].opens += nms
            continue
        if word == "set_option" and is_prefix:
            continue
        hm = HEAD.match(chunk_m.lstrip())
        if not hm:
            prefix_omit, prefix_open, prefix_include = [], [], []
            continue
        lead = len(chunk_m) - len(chunk_m.lstrip())
        kw = " ".join(hm.group("kw").split())
        if kw == "example":
            prefix_omit, prefix_open, prefix_include = [], [], []
            continue
        after = b + lead + hm.end()
        rest_m = masked[after:b + len(chunk_m)]
        names = []
        if kw == "alias":
            m2 = re.match(r"\s*⟨(.*?)⟩", rest_m)
            if m2:
                names = [t.strip() for t in m2.group(1).split(",") if t.strip() and t.strip() != "_"]
            else:
                m2 = re.match(r"\s*(" + _N + ")", rest_m)
                names = [m2.group(1)] if m2 else []
        elif kw == "instance":
            r2 = re.sub(r"^\s*\(priority\s*:=\s*[^)]*\)", "", rest_m)
            m2 = re.match(r"\s*(" + _N + r")\s*(?=[:(\[{⦃]|$)", r2)
            names = [m2.group(1)] if m2 else []
        else:
            m2 = re.match(r"\s*(" + _N + ")", rest_m)
            names = [m2.group(1)] if m2 else []
        # doc comment immediately before the declaration
        doc = ""
        k = b
        while k > 0 and text[k - 1] in " \t\n":
            k -= 1
        if k in doc_by_end:
            doc = doc_by_end[k][1]
        else:
            # attributes may come after the doc comment on separate lines
            pass
        decl_text = chunk
        line = line_of(b + lead + len(hm.group("prefix")))
        space = ns()
        opens = [o for s in scopes for o in s.opens] + prefix_open
        if kw in DEF_KINDS:
            stmt_end = None
        else:
            stmt_end = _scan_to(masked, after, stop_at_bar=True)
            if stmt_end is not None and stmt_end > b + len(chunk_m):
                stmt_end = None
        statement = text[b:stmt_end].rstrip() if stmt_end is not None else decl_text
        sig_m = mask(statement)
        variables = _relevant_variables(
            [v for s in scopes for v in s.variables], ATTRS.sub("", sig_m), prefix_omit,
            [i for s in scopes for i in s.included] + prefix_include)
        for nm in names:
            full = nm[len("_root_."):] if nm.startswith("_root_.") else (
                f"{space}.{nm}" if space else nm)
            d = Decl(name=full, kind=kw, package=package, path=path, line=line, doc=doc,
                     text=decl_text, statement=statement, variables=variables, namespace=space,
                     opens=opens, private="private" in hm.group("prefix").split())
            decls.append(d)
            if kw in ("structure", "class", "inductive", "class inductive"):
                decls += _members(d, masked[b:b + len(chunk_m)], text[b:b + len(chunk_m)], line)
        prefix_omit, prefix_open, prefix_include = [], [], []
    return decls


def _members(parent, chunk_m, chunk, line0):
    """Fields and constructors of a structure, class or inductive type."""
    out = []
    lines_m = chunk_m.split("\n")
    lines = chunk.split("\n")
    if parent.kind in ("inductive", "class inductive"):
        for k, ln in enumerate(lines_m):
            m = re.match(r"^\s*\|\s*(" + _N + ")", ln)
            if m:
                out.append(Decl(name=f"{parent.name}.{m.group(1)}", kind="constructor",
                                package=parent.package, path=parent.path, line=line0 + k,
                                doc="", text=parent.text, statement=parent.text,
                                variables=parent.variables, namespace=parent.namespace,
                                opens=parent.opens, parent=parent.name))
        return out
    # structure / class: after the first `where`
    w = _scan_to(chunk_m, 0)
    ctor = "mk"
    if w is None:
        return out
    after = chunk_m[w:]
    first_line = line0 + chunk_m[:w].count("\n")
    for k, ln in enumerate(after.split("\n")):
        if k == 0:
            ln = ln[5:] if ln.startswith("where") else ln
        m = re.match(r"^\s*(" + _N + r")\s*::", ln)
        if m:
            ctor = m.group(1)
            continue
        m = re.match(r"^(\s+)((?:" + _N + r"\s+)*" + _N + r")\s*(?=[:(\[{⦃]|$)", ln)
        if m and len(m.group(1)) <= 4 and m.group(2) not in LEAN_KEYWORDS and ln.strip():
            # an indented field line `name : type` or `name (binders) : type`
            if ":" not in ln and not re.search(r"[(\[{⦃]", ln):
                continue
            for nm in m.group(2).split():
                out.append(Decl(name=f"{parent.name}.{nm}", kind="field", package=parent.package,
                                path=parent.path, line=first_line + k, doc="", text=parent.text,
                                statement=parent.text, variables=parent.variables,
                                namespace=parent.namespace, opens=parent.opens,
                                parent=parent.name))
    out.append(Decl(name=f"{parent.name}.{ctor}", kind="constructor", package=parent.package,
                    path=parent.path, line=line0, doc="", text=parent.text,
                    statement=parent.text, variables=parent.variables,
                    namespace=parent.namespace, opens=parent.opens, parent=parent.name))
    return out


def lean_files(root):
    """The Lean source files of the packages (top-level directories with a lakefile),
    skipping hidden directories such as `.lake`."""
    root = Path(root)
    out = []
    for pkg in sorted(p for p in root.iterdir() if p.is_dir() and not p.name.startswith(".")):
        if not ((pkg / "lakefile.toml").is_file() or (pkg / "lakefile.lean").is_file()):
            continue
        for dirpath, dirnames, filenames in os.walk(pkg):
            dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
            for f in sorted(filenames):
                if f.endswith(".lean") and f != "lakefile.lean":
                    out.append(Path(dirpath) / f)
    return out


class Index:
    """All declarations of the library, by fully qualified name."""

    def __init__(self, decls):
        self.by_name = {}
        self.duplicates = {}
        for d in decls:
            old = self.by_name.get(d.name)
            if old is None:
                self.by_name[d.name] = d
            else:
                self.duplicates.setdefault(d.name, [old]).append(d)
                if old.private and not d.private:
                    self.by_name[d.name] = d
        self._refs = {}
        suffix = {}
        for name in self.by_name:
            parts = name.split(".")
            for k in range(1, len(parts)):
                suffix.setdefault(".".join(parts[k:]), []).append(name)
        self._suffix = suffix

    def get(self, name):
        return self.by_name.get(name)

    def resolve(self, ident, namespace, opens):
        """The library declaration an identifier denotes in a namespace with opens, or None."""
        cands = []
        parts = namespace.split(".") if namespace else []
        for k in range(len(parts), -1, -1):
            pre = ".".join(parts[:k])
            cands.append(f"{pre}.{ident}" if pre else ident)
        for o in opens:
            cands.append(f"{o}.{ident}")
            for k in range(len(parts), 0, -1):
                cands.append(".".join(parts[:k]) + f".{o}.{ident}")
        for c in cands:
            if c in self.by_name:
                return c
        return None

    def refs(self, d):
        """Library declarations used by the statement of d (and by the variables it uses)."""
        if d.name not in self._refs:
            self._refs[d.name] = self._compute_refs(d)
        return self._refs[d.name]

    def _compute_refs(self, d):
        src = ATTRS.sub("", mask(d.statement))
        hm = HEAD.match(src.lstrip())
        if hm:
            src = src.lstrip()[hm.end():]
            # drop the declaration's own name
            src = re.sub(r"^\s*" + _N, " ", src, count=1)
        src = src + "\n" + "\n".join(d.variables)
        bound = _bound_names(src)
        refs = []
        for ident in IDENT.findall(src):
            if ident in LEAN_KEYWORDS:
                continue
            hit = None
            if ident.split(".")[0] in bound:
                rest = ident.split(".", 1)[1] if "." in ident else ""
                if rest:
                    c = self._suffix.get(rest, [])
                    if len(c) == 1:
                        hit = c[0]
            else:
                hit = self.resolve(ident, d.namespace, d.opens)
                if hit is None and "." in ident:
                    # generalized field notation on a resolved head: x.f with x a library name
                    head, rest = ident.rsplit(".", 1)
                    if self.resolve(head, d.namespace, d.opens):
                        c = self._suffix.get(rest, [])
                        hit = c[0] if len(c) == 1 else None
                    else:
                        c = self._suffix.get(rest, [])
                        hit = c[0] if len(c) == 1 else None
            if hit and hit != d.name and hit not in refs:
                refs.append(hit)
        return refs


def build_index(root):
    root = Path(root)
    decls = []
    for p in lean_files(root):
        rel = p.relative_to(root)
        decls += parse_file(p.read_text(encoding="utf-8"), rel.parts[0], str(rel))
    return Index(decls)
