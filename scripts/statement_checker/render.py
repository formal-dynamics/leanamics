"""Text of the detail view (`--show`), of the Markdown context (`--context`) and of the reports.

The detail view is a list of `(text, style)` lines; the plain output ignores the styles. Styles: title, h, dim, code, doc, ok, bad, warn, link, key, text.
"""
import re
import textwrap
import unicodedata

from . import checks, latex

WIDE = ("W", "F")


def cwidth(s):
    """Display width of a string in a terminal cell grid."""
    w = 0
    for ch in s:
        if unicodedata.combining(ch) or ch in "​‍":
            continue
        w += 2 if unicodedata.east_asian_width(ch) in WIDE else 1
    return w


def clip(s, width):
    """The longest prefix of s that fits in width cells."""
    out, w = [], 0
    for ch in s:
        cw = 0 if unicodedata.combining(ch) else (2 if unicodedata.east_asian_width(ch) in WIDE else 1)
        if w + cw > width:
            break
        out.append(ch)
        w += cw
    return "".join(out)


def pad(s, width):
    s = clip(s, width)
    return s + " " * (width - cwidth(s))


def fit(s, width):
    """s in exactly width cells, cut with an ellipsis and followed by a space if needed."""
    if width <= 0:
        return ""
    if cwidth(s) <= width - 1:
        return pad(s, width)
    return pad(clip(s, width - 2) + "…", width)


def wrap(text, width, indent="", subsequent=None):
    """Wrap prose paragraph by paragraph, keeping explicit line breaks."""
    subsequent = indent if subsequent is None else subsequent
    out = []
    for para in text.split("\n"):
        if not para.strip():
            out.append("")
            continue
        lead = para[:len(para) - len(para.lstrip())]
        out += textwrap.wrap(para.strip(), width=max(10, width), initial_indent=indent + lead,
                             subsequent_indent=subsequent + lead, break_on_hyphens=False,
                             break_long_words=True) or [indent]
    return out


def wrap_code(text, width, indent="  ", marker="↪ "):
    """Hard-wrap code lines that do not fit, marking the continuation with ↪."""
    out = []
    w = max(10, width - len(indent))
    for line in text.rstrip("\n").split("\n"):
        line = line.rstrip()
        first = True
        while True:
            head = clip(line, w if first else w - cwidth(marker))
            out.append(indent + ("" if first else marker) + head)
            line = line[len(head):]
            first = False
            if not line:
                break
    return out


def prose(doc):
    """A doc comment as prose: single line breaks become spaces (paragraphs, list items and
    indented code lines keep theirs)."""
    return re.sub(r"(?<!\n)\n(?!\n|\s*[-*•+]\s|\s*\d+[.)]\s|    )", " ", doc.strip())


def tex(s):
    return latex.render(s, code=lambda x: x)


def status_words(st):
    parts = []
    if st.agrees:
        parts.append("agrees: " + ", ".join(st.agrees))
    if st.differs:
        parts.append("differs: " + ", ".join(st.differs))
    if st.unsure:
        parts.append("unsure: " + ", ".join(st.unsure))
    if st.stale:
        parts.append("stale: " + ", ".join(st.stale))
    return "; ".join(parts) if parts else "not checked yet"


def detail(model, e, width=80, raw=False):
    """The lines of the detail view of entry e."""
    from .model import TIERS
    L = []
    add = lambda text, style="text": L.append((text, style))
    it = e.item
    W = max(30, width - 1)

    def section(title):
        add("")
        title = clip(title, W - 4)
        add("── " + title + " " + "─" * max(0, W - cwidth(title) - 4), "h")

    add(f"{it.package} · {it.label} · {it.env}", "title")
    for ln in wrap(tex(it.title) or "(no title)", W):
        add(ln, "title")
    add(f"priority: {TIERS[e.tier]}", "dim")
    st = model.status(e)
    style = "bad" if st.differs else "warn" if (st.unsure or st.stale) else "ok" if st.n else "dim"
    for ln in wrap("status: " + status_words(st), W):
        add(ln, style)
    if st.mine is not None:
        mine = f"your latest check: {st.mine.verdict} on {st.mine.date[:10]}"
        if st.mine_stale:
            mine += " (stale: " + ", ".join(checks.stale_parts(st.mine, e.lean_hash, e.source_hash)) + " changed since)"
        add(mine, "warn" if st.mine_stale else "dim")

    # ---- source
    section("SOURCE")
    if e.sources:
        for s in e.sources:
            ref = s.get("paper", "")
            if s.get("venue"):
                ref += f", {s['venue']}"
            for ln in wrap(ref, W, "  "):
                add(ln, "text")
            where = s.get("result", "")
            if s.get("version"):
                where += f", {s['version']}"
            if s.get("page"):
                where += f", p. {s['page']}"
            add("  " + where, "key")
            if s.get("url"):
                for ln in wrap_code(s["url"], W, "  ", ""):
                    add(ln, "link")
            add("  [" + s.get("status", "status unknown") + "]", "warn")
            if s.get("statement"):
                add("  Original statement:", "dim")
                body = s["statement"] if raw else tex(s["statement"])
                for ln in (wrap_code(body, W, "    ") if raw else wrap(body, W, "    ")):
                    add(ln, "text")
            if s.get("context"):
                add("  Context:", "dim")
                body = s["context"] if raw else tex(s["context"])
                for ln in (wrap_code(body, W, "    ") if raw else wrap(body, W, "    ")):
                    add(ln, "dim")
            if s.get("notes"):
                for ln in wrap("Notes: " + s["notes"], W, "  ", "    "):
                    add(ln, "dim")
            add("")
    else:
        add("  No transcribed original statement (verification/sources.toml).", "dim")
    for r in e.provenance:
        add(f"  {r.file}:{r.line} ({r.heading})", "dim")
        for h, c in zip(r.header, r.cells):
            if h in ("Source", "Constants", "Size hypothesis", "Population size it means"):
                for ln in wrap(f"{h}: {c}", W, "    ", "      "):
                    add(ln, "text")
    for r in e.readme:
        add(f"  {r.file}:{r.line}", "dim")
        for ln in wrap(r.text(), W, "    ", "      "):
            add(ln, "text")
    if it.section:
        for ln in wrap("Blueprint section: " + tex(it.section), W, "  ", "    "):
            add(ln, "text")
    ab = model.abstracts.get(it.package, "")
    if ab:
        first = tex(ab).split(". ")
        summary = ". ".join(first[:2]).strip()
        if summary and not summary.endswith("."):
            summary += "."
        for ln in wrap("Package (blueprint abstract): " + summary, W, "  ", "    "):
            add(ln, "dim")
    for u in e.links():
        for ln in wrap_code(u, W, "  ", ""):
            add(ln, "link")

    # ---- blueprint
    section(f"BLUEPRINT STATEMENT  {it.path}:{it.line}")
    body = it.statement if raw else tex(it.statement)
    for ln in (wrap_code(body, W, "  ") if raw else wrap(body, W, "  ")):
        add(ln, "text")
    if it.uses:
        for ln in wrap("uses: " + ", ".join(it.uses), W, "  ", "    "):
            add(ln, "dim")

    # ---- Lean
    section("LEAN")
    for k, (name, d) in enumerate(e.decls):
        if d is None:
            for ln in wrap(f"[{k + 1}] {name}: NOT FOUND in the Lean sources", W, "  ", "      "):
                add(ln, "bad")
            continue
        for ln in wrap(f"[{k + 1}] {name}  ({d.kind})", W, "  ", "      "):
            add(ln, "key")
        for ln in wrap(f"{d.path}:{d.line}" + ("  (Mathlib)" if d.package == "mathlib" else ""),
                       W, "      "):
            add(ln, "dim")
        if d.parent:
            add(f"      member of {d.parent}", "dim")
        if d.doc:
            for ln in wrap("/-- " + prose(d.doc) + " -/", W, "    "):
                add(ln, "doc")
        if d.variables:
            for ln in wrap("variable " + " ".join(d.variables), W, "    ", "        "):
                add(ln, "code")
        for ln in wrap_code(d.statement + (" := …" if d.statement != d.text else ""), W, "    "):
            add(ln, "code")
        add("")

    # ---- definitions used
    section("DEFINITIONS USED BY THE STATEMENT (press D to open one)")
    defs = used_definitions(model, e)
    if not defs:
        add("  none found", "dim")
    for k, (name, d, target) in enumerate(defs):
        where = f"{d.path}:{d.line}" if d else ""
        tag = ""
        if target is not None:
            tst = model.status(target)
            tag = f"→ {target.id}" + (f" ✓{tst.n}" if tst.n else " (unchecked)")
        else:
            tag = "(not a blueprint item)"
        for ln in wrap(f"{k + 1:>2}. {name}  {d.kind if d else ''}", W, "  ", "      "):
            add(ln, "key")
        for ln in wrap(f"{where}  {tag}", W, "      ", "        "):
            add(ln, "dim")

    # ---- checks
    section("CHECKS")
    recs = sorted(model.store.for_item(e.id), key=lambda c: c.date)
    if not recs:
        add("  none recorded", "dim")
    for c in recs:
        stale = checks.stale_parts(c, e.lean_hash, e.source_hash)
        style = {"agrees": "ok", "differs": "bad", "unsure": "warn"}[c.verdict]
        line = f"  {c.date[:10]}  {c.reviewer}: {c.verdict}"
        if stale:
            line += "  [stale: " + " and ".join(stale) + " changed since]"
            style = "dim"
        add(line, style)
        if c.comment:
            for ln in wrap(c.comment, W, "      "):
                add(ln, "text")
    add("")
    add(f"  hashes now: Lean {e.lean_hash}, source {e.source_hash}", "dim")
    return L


def used_definitions(model, e):
    """(name, Decl, Entry or None) for the library definitions used by the statement, then
    the other library declarations it uses."""
    out = []
    for n in e.used:
        d = model.index.get(n)
        if d is None:
            continue
        pk = e.item.package
        target = model.item_for_decl(n, pk) or (model.item_for_decl(d.parent, pk) if d.parent else None)
        out.append((n, d, target))
    out.sort(key=lambda t: (not t[1].is_definition,))
    return out


def decl_lines(model, d, width=80):
    """Pager lines for a declaration that is not a blueprint item."""
    W = max(30, width - 1)
    L = [(f"{d.name}  ({d.kind})", "title"), (f"{d.path}:{d.line}", "dim"),
         ("This declaration is not named by any blueprint item.", "warn"), ("", "text")]
    if d.doc:
        L += [(ln, "doc") for ln in wrap("/-- " + prose(d.doc) + " -/", W, "  ")]
    if d.variables:
        L += [(ln, "code") for ln in wrap("variable " + " ".join(d.variables), W, "  ", "      ")]
    L += [(ln, "code") for ln in wrap_code(d.text, W, "  ")]
    refs = model.index.refs(d)
    if refs:
        L += [("", "text"), ("Uses: " + ", ".join(refs), "dim")]
    return L


def item_context(model, e, question=""):
    """An item as Markdown, with the full definitions its statement uses (`--context`)."""
    it = e.item
    out = ["# Checking a Lean statement against its source", ""]
    out.append("You help a reviewer check that a statement of the Leanamics library (Lean 4 + "
               "Mathlib) says what the source paper says. Answer in plain text. Be concrete: "
               "explain the Lean statement in words, say which hypotheses and conclusions "
               "correspond, and list every difference (explicit constants, extra or missing "
               "hypotheses, different quantifiers, different definitions). Say when you are "
               "unsure.")
    out.append("")
    if question.strip():
        out += ["## Question of the reviewer", "", question.strip(), ""]
    out += [f"## Item {e.id} ({it.env}): {it.title}", ""]
    out += ["## Source", ""]
    for s in e.sources:
        out.append(f"- {s.get('paper', '')}, {s.get('venue', '')}; {s.get('result', '')}, "
                   f"{s.get('version', '')} ({s.get('status', '')})")
        if s.get("statement"):
            out += ["", "Original statement (LaTeX):", "", "```latex", s["statement"], "```"]
        if s.get("context"):
            out += ["", "Context (LaTeX):", "", "```latex", s["context"], "```"]
        if s.get("notes"):
            out += ["", "Notes: " + s["notes"]]
        out.append("")
    for r in e.provenance:
        out += [f"From {r.file}:", "", r.text(skip=("Proof", "Produced by")), ""]
    for r in e.readme:
        out += [f"From {r.file}:", "", r.text(), ""]
    out += ["## Blueprint statement (a paraphrase written for the formalization)", "",
            "```latex", it.statement, "```", ""]
    out += ["## Lean declarations", ""]
    for name, d in e.decls:
        if d is None:
            out += [f"- {name}: not found", ""]
            continue
        out += [f"### {name} ({d.kind}, {d.path}:{d.line})", "", "```lean"]
        if d.variables:
            out.append("variable " + " ".join(d.variables))
        if d.doc:
            out.append("/-- " + d.doc + " -/")
        out += [d.statement, "```", ""]
    defs = used_definitions(model, e)
    if defs:
        out += ["## Library definitions used by the statement", ""]
        for n, d, _ in defs:
            if not d.is_definition:
                continue
            out += [f"### {n} ({d.kind}, {d.path}:{d.line})", "", "```lean"]
            if d.variables:
                out.append("variable " + " ".join(d.variables))
            if d.doc:
                out.append("/-- " + d.doc + " -/")
            out += [d.text, "```", ""]
    return "\n".join(out)
