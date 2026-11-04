"""The curses app: a list of items with filters, a detail view, and check recording."""
import curses
import locale
import os
import subprocess
import tempfile
import webbrowser

from . import checks, render
from .model import TIERS

FILTERS = ["all", "unchecked", "unchecked by me", "stale", "differs", "unsure"]
SORTS = ["priority", "blueprint"]

HELP = """\
Leanamics statement checker

A check records that you compared the Lean statement of an item with its source
(the original statement, or the paper), not with the blueprint paraphrase only.
Definitions matter as much as theorems: open the definitions an item uses (D).

LIST VIEW
  ↑ ↓ j k          move              PgUp PgDn       page
  Home End g G     first / last      Enter → l       open the item
  /                search (label, title, Lean names, text); Esc clears it
  f  F             next / previous filter: all, unchecked, unchecked by me,
                   stale, differs, unsure (or 1-6)
  p  P             next / previous package (0: all packages)
  s                sort: priority (main results and the definitions they use
                   first) or blueprint order
  t                progress per package
  q                quit

DETAIL VIEW
  ↑ ↓ j k PgUp PgDn Space Home End     scroll
  n  N             next / previous item of the list
  a                record: the Lean statement AGREES with the source
  d                record: it DIFFERS (comment required: what differs, and
                   whether it is intended, e.g. explicit constants)
  u                record: UNSURE (comment required: your question)
  D                open a definition used by the statement
  r                toggle rendered / LaTeX source
  A                ask an assistant about the item ($CHECK_STATEMENTS_ASK_CMD)
  L                ask Lean for the elaborated types (#check, slow)
  o                open the first link in a browser
  Esc ← q          back

Checks are appended to verification/checks/<your-name>.jsonl. Commit that file.
A check becomes stale when the Lean text or the source text of the item changes.
"""

STYLE_COLORS = {
    # style: (fg, attr)
    "title": (curses.COLOR_CYAN, curses.A_BOLD),
    "h": (curses.COLOR_BLUE, curses.A_BOLD),
    "dim": (None, curses.A_DIM),
    "code": (curses.COLOR_YELLOW, 0),
    "doc": (curses.COLOR_GREEN, curses.A_DIM),
    "ok": (curses.COLOR_GREEN, curses.A_BOLD),
    "bad": (curses.COLOR_RED, curses.A_BOLD),
    "warn": (curses.COLOR_MAGENTA, curses.A_BOLD),
    "link": (curses.COLOR_CYAN, curses.A_UNDERLINE),
    "key": (curses.COLOR_WHITE, curses.A_BOLD),
    "text": (None, 0),
    "bar": (curses.COLOR_WHITE, curses.A_REVERSE),
    "sel": (curses.COLOR_BLACK, curses.A_REVERSE),
}


class App:
    def __init__(self, scr, model, color=True):
        self.scr = scr
        self.m = model
        self.filter = 0
        self.pkg = 0          # 0: all packages
        self.sort = 0
        self.query = ""
        self.sel = 0
        self.top = 0
        self.message = ""
        self.attrs = {}
        self.statuses = {}
        self.color = color and curses.has_colors()
        self.snapshot = os.environ.get("CHECK_STATEMENTS_SNAPSHOT")
        self.shadow = []
        self._init_colors()
        self.refresh_status()
        self.apply()

    # ------------------------------------------------------------------ setup
    def _init_colors(self):
        if self.color:
            try:
                curses.start_color()
                curses.use_default_colors()
                bg = -1
            except curses.error:
                bg = curses.COLOR_BLACK
        for k, (name, (fg, attr)) in enumerate(STYLE_COLORS.items()):
            a = attr
            if self.color and fg is not None:
                try:
                    curses.init_pair(k + 1, fg, bg)
                    a |= curses.color_pair(k + 1)
                except curses.error:
                    pass
            if name == "bar":
                a = curses.A_REVERSE | curses.A_BOLD
            if name == "sel":
                a = curses.A_REVERSE
            self.attrs[name] = a

    def refresh_status(self):
        self.statuses = {e.id: self.m.status(e) for e in self.m.entries}

    # ------------------------------------------------------------------ data
    def packages(self):
        return ["all"] + self.m.packages()

    def matches(self, e):
        st = self.statuses[e.id]
        f = FILTERS[self.filter]
        if f == "unchecked" and st.n:
            return False
        if f == "unchecked by me":
            mine = st.mine
            if mine is not None and not st.mine_stale and mine.verdict != "unsure":
                return False
        if f == "stale" and not st.stale:
            return False
        if f == "differs" and not st.differs:
            return False
        if f == "unsure" and not st.unsure:
            return False
        pk = self.packages()[self.pkg]
        if pk != "all" and e.item.package != pk:
            return False
        if self.query:
            text = e.search_text()
            if not all(w in text for w in self.query.lower().split()):
                return False
        return True

    def apply(self, keep=None):
        base = self.m.priority if SORTS[self.sort] == "priority" else self.m.entries
        self.rows = [e for e in base if self.matches(e)]
        self.sel = 0
        if keep is not None:
            for k, e in enumerate(self.rows):
                if e.id == keep:
                    self.sel = k
        self.top = min(self.top, max(0, self.sel))

    # ------------------------------------------------------------------ drawing
    def put(self, y, x, text, style="text", width=None):
        h, w = self.scr.getmaxyx()
        if y < 0 or y >= h or x >= w:
            return
        width = w - x if width is None else min(width, w - x)
        if y == h - 1:
            width = min(width, w - x - 1)  # never write the bottom-right cell
        if width <= 0:
            return
        text = render.clip(text, width)
        try:
            self.scr.addstr(y, x, text, self.attrs.get(style, 0))
        except curses.error:
            pass
        if self.snapshot is not None:
            self._shadow_put(y, x, text)

    def _shadow_put(self, y, x, text):
        """Keep a copy of the screen as text, for tests and snapshots."""
        h, w = self.scr.getmaxyx()
        if len(self.shadow) != h or (self.shadow and len(self.shadow[0]) != w):
            self.shadow = [[" "] * w for _ in range(h)]
        row = self.shadow[y]
        for ch in text:
            if x >= w:
                break
            if render.cwidth(ch) == 0 and x > 0:
                row[x - 1] += ch
                continue
            row[x] = ch
            if render.cwidth(ch) == 2 and x + 1 < w:
                row[x + 1] = ""
                x += 1
            x += 1

    def erase(self):
        self.scr.erase()
        if self.snapshot is not None:
            h, w = self.scr.getmaxyx()
            self.shadow = [[" "] * w for _ in range(h)]

    def refresh(self):
        self.scr.refresh()
        if self.snapshot:
            with open(self.snapshot, "w", encoding="utf-8") as f:
                f.write("\n".join("".join(r).rstrip() for r in self.shadow) + "\n")

    def bar(self, y, text, right=""):
        h, w = self.scr.getmaxyx()
        r = render.clip(right, max(0, w // 2))
        left = render.clip(text, max(0, w - render.cwidth(r) - 1))
        line = left + " " * max(0, w - render.cwidth(left) - render.cwidth(r)) + r
        self.put(y, 0, line, "bar", w)

    def status_cell(self, st):
        """(text, style) of the status column (4 cells)."""
        if st.differs:
            return "≠" + str(st.n), "bad"
        if st.unsure:
            return "?" + (str(st.n) if st.n else " "), "warn"
        if st.stale and not st.n:
            return "~ ", "warn"
        if st.n:
            return "✓" + str(st.n), "ok"
        return "· ", "dim"

    def draw_list(self):
        self.erase()
        h, w = self.scr.getmaxyx()
        rows = self.rows
        n_done = sum(1 for e in rows if self.statuses[e.id].n)
        pk = self.packages()[self.pkg]
        title = f" Leanamics statements │ {FILTERS[self.filter]} │ {pk} │ {SORTS[self.sort]}"
        if self.query:
            title += f" │ /{self.query}"
        self.bar(0, title, f"{self.m.reviewer or '(no reviewer)'} ")
        body_h = h - 4
        if body_h < 1:
            self.put(0, 0, "terminal too small")
            return
        if self.sel < self.top:
            self.top = self.sel
        if self.sel >= self.top + body_h:
            self.top = self.sel - body_h + 1
        wide = w >= 120
        # columns: marker(1) status(3) package(10) kind(4) label(L) title
        lab_w = 28 if w >= 100 else 20
        pkg_w = 10
        for k in range(body_h):
            idx = self.top + k
            y = k + 1
            if idx >= len(rows):
                break
            e = rows[idx]
            st = self.statuses[e.id]
            selected = idx == self.sel
            mark = "★" if e.tier == 0 else "◆" if e.tier == 1 else " "
            sc, ss = self.status_cell(st)
            x = 0
            if selected:
                self.put(y, 0, " " * w, "sel")
            def cell(text, width, style):
                nonlocal x
                self.put(y, x, render.fit(text, width), "sel" if selected else style, width)
                x += width
            cell(mark, 2, "warn")
            cell(sc, 4, ss)
            cell(e.item.package, pkg_w, "dim")
            cell(e.kind, 5, "code" if e.is_definition else "key")
            cell(e.item.label, lab_w, "text")
            rest = w - x
            title = render.tex(e.item.title)
            if wide:
                names = ", ".join(n.rsplit(".", 1)[-1] for n in e.item.lean)
                tw = max(20, rest // 2)
                cell(title, tw, "text")
                cell(" " + names, max(0, w - x), "dim")
            else:
                cell(title, max(0, rest), "text")
        # footer: the selected item, then progress or a message
        total = len(self.m.entries)
        ndone_all = sum(1 for s in self.statuses.values() if s.n)
        n2 = sum(1 for s in self.statuses.values() if s.n >= 2)
        pos = f"{self.sel + 1 if rows else 0}/{len(rows)}"
        self.put(h - 3, 0, "─" * w, "dim")
        if rows:
            e = rows[self.sel]
            st = self.statuses[e.id]
            info = f" {e.id} │ {TIERS[e.tier]} │ {render.status_words(st)}"
            ss = self.status_cell(st)[1]
        else:
            info, ss = " no items match (f: filter, 0: all packages, Esc: clear search)", "warn"
        self.put(h - 2, 0, info, ss if ss != "dim" else "text")
        prog = f" {pos} │ checked: {n_done} here, {ndone_all}/{total} by ≥1, {n2} by ≥2 │"
        if w >= 120:
            prog += " ★ main ◆ used by main │ Enter open / search f filter p package s sort t progress q quit"
        else:
            prog += " Enter / f p s t q"
        self.bar(h - 1, self.message or prog, " ? help ")
        self.message = ""

    # ------------------------------------------------------------------ prompts
    def prompt(self, label, initial=""):
        """A one-line editor on the last line. Returns the text, or None on Esc."""
        h, w = self.scr.getmaxyx()
        buf = list(initial)
        pos = len(buf)
        curses.curs_set(1)
        try:
            while True:
                lw = render.cwidth(label)
                avail = max(5, w - lw - 2)
                start = max(0, pos - avail + 1)
                shown = "".join(buf[start:start + avail])
                self.put(h - 1, 0, " " * (w - 1), "text")
                self.put(h - 1, 0, label, "key")
                self.put(h - 1, lw, shown, "text")
                try:
                    self.scr.move(h - 1, min(w - 2, lw + render.cwidth("".join(buf[start:pos]))))
                except curses.error:
                    pass
                self.refresh()
                ch = self.scr.get_wch()
                if ch in ("\n", "\r", curses.KEY_ENTER):
                    return "".join(buf)
                if ch == "\x1b":
                    return None
                if ch in (curses.KEY_BACKSPACE, "\x7f", "\b", "\x08"):
                    if pos:
                        del buf[pos - 1]
                        pos -= 1
                elif ch == curses.KEY_DC:
                    if pos < len(buf):
                        del buf[pos]
                elif ch == curses.KEY_LEFT:
                    pos = max(0, pos - 1)
                elif ch == curses.KEY_RIGHT:
                    pos = min(len(buf), pos + 1)
                elif ch in (curses.KEY_HOME, "\x01"):
                    pos = 0
                elif ch in (curses.KEY_END, "\x05"):
                    pos = len(buf)
                elif ch == "\x15":  # Ctrl-U
                    buf, pos = [], 0
                elif ch == curses.KEY_RESIZE:
                    h, w = self.scr.getmaxyx()
                elif isinstance(ch, str) and ch.isprintable():
                    buf.insert(pos, ch)
                    pos += 1
        finally:
            curses.curs_set(0)

    def confirm(self, label):
        h, w = self.scr.getmaxyx()
        self.put(h - 1, 0, " " * (w - 1), "text")
        self.put(h - 1, 0, label + " [y/N] ", "key")
        self.refresh()
        ch = self.scr.get_wch()
        return ch in ("y", "Y")

    def choose(self, title, options):
        """A selectable list of (label, style) in the whole screen. Returns an index or None."""
        sel, top = 0, 0
        while True:
            self.erase()
            h, w = self.scr.getmaxyx()
            self.bar(0, " " + title)
            body = h - 2
            if sel < top:
                top = sel
            if sel >= top + body:
                top = sel - body + 1
            for k in range(body):
                i = top + k
                if i >= len(options):
                    break
                label, style = options[i]
                self.put(k + 1, 0, render.pad(" " + label, w), "sel" if i == sel else style, w)
            self.bar(h - 1, " ↑↓ move  Enter open  Esc back")
            self.refresh()
            ch = self.scr.get_wch()
            if ch in (curses.KEY_UP, "k"):
                sel = max(0, sel - 1)
            elif ch in (curses.KEY_DOWN, "j"):
                sel = min(len(options) - 1, sel + 1)
            elif ch == curses.KEY_NPAGE:
                sel = min(len(options) - 1, sel + body)
            elif ch == curses.KEY_PPAGE:
                sel = max(0, sel - body)
            elif ch in ("\n", "\r", curses.KEY_ENTER, curses.KEY_RIGHT, "l"):
                return sel if options else None
            elif ch in ("\x1b", "q", curses.KEY_LEFT, "h"):
                return None

    # ------------------------------------------------------------------ pager
    def pager(self, title, make_lines, keys=None, footer=" ↑↓ PgUp PgDn scroll  Esc back"):
        """Show lines produced by make_lines(width); keys maps a key to a handler that
        returns 'back', 'redraw' or None."""
        y = 0
        while True:
            h, w = self.scr.getmaxyx()
            lines = make_lines(w)
            body = h - 2
            y = max(0, min(y, max(0, len(lines) - body)))
            self.erase()
            name = title() if callable(title) else title
            self.bar(0, " " + name, f"{min(len(lines), y + body)}/{len(lines)} ")
            for k in range(body):
                if y + k >= len(lines):
                    break
                text, style = lines[y + k]
                self.put(k + 1, 0, text, style)
            self.bar(h - 1, self.message or footer)
            self.message = ""
            self.refresh()
            ch = self.scr.get_wch()
            if ch in (curses.KEY_DOWN, "j"):
                y += 1
            elif ch in (curses.KEY_UP, "k"):
                y -= 1
            elif ch in (curses.KEY_NPAGE, " "):
                y += body - 1
            elif ch in (curses.KEY_PPAGE, "b"):
                y -= body - 1
            elif ch in (curses.KEY_HOME, "g"):
                y = 0
            elif ch in (curses.KEY_END, "G"):
                y = len(lines)
            elif ch == curses.KEY_RESIZE:
                pass
            elif keys and ch in keys:
                r = keys[ch]()
                if r == "back":
                    return
                if r == "top":
                    y = 0
            elif ch in ("\x1b", "q", curses.KEY_LEFT, "h"):
                return

    def text_pager(self, title, text):
        self.pager(title, lambda w: [(ln, "text") for ln in render.wrap(text, w - 1)])

    # ------------------------------------------------------------------ detail
    def detail(self, start):
        """The detail view of rows[start]; n/N move through the list."""
        state = {"idx": start, "raw": False, "entry": self.rows[start] if self.rows else None}

        def lines(w):
            return render.detail(self.m, state["entry"], w, raw=state["raw"])

        def move(step):
            if not self.rows:
                return None
            i = state["idx"]
            # the current entry may come from another list (definitions); go back to the list
            i = max(0, min(len(self.rows) - 1, i + step))
            state["idx"] = i
            state["entry"] = self.rows[i]
            self.sel = i
            return "top"

        def record(verdict):
            e = state["entry"]
            if not self.m.reviewer:
                self.message = " No reviewer name: start with --reviewer NAME"
                return None
            need = verdict in checks.NEEDS_COMMENT
            label = {"agrees": "Agrees. Optional comment (Enter saves, Esc cancels): ",
                     "differs": "Differs. What differs, and is it intended? (Esc cancels): ",
                     "unsure": "Unsure. Your question (Esc cancels): "}[verdict]
            comment = ""
            while True:
                comment = self.prompt(label, comment)
                if comment is None:
                    self.message = " Cancelled, nothing recorded"
                    return None
                if need and not comment.strip():
                    label = f"A comment is required for `{verdict}`: "
                    continue
                break
            self.m.record(e, verdict, comment)
            self.statuses[e.id] = self.m.status(e)
            self.message = f" Recorded `{verdict}` for {e.id} as {self.m.reviewer}"
            return None

        def open_def():
            e = state["entry"]
            defs = render.used_definitions(self.m, e)
            if not defs:
                self.message = " This statement uses no library declaration"
                return None
            opts = []
            for n, d, target in defs:
                tag = f"→ {target.id}" if target else "(not an item)"
                opts.append((f"{n}  [{d.kind}]  {tag}", "text" if d.is_definition else "dim"))
            k = self.choose(f"Library declarations used by {e.id}", opts)
            if k is None:
                return None
            n, d, target = defs[k]
            if target is not None:
                self.sub_detail(target)
            else:
                self.pager(n, lambda w: render.decl_lines(self.m, d, w))
            return None

        def toggle_raw():
            state["raw"] = not state["raw"]
            self.message = " Showing LaTeX source" if state["raw"] else " Showing rendered text"

        def open_link():
            urls = state["entry"].links()
            if not urls:
                self.message = " No link known for this item"
                return None
            try:
                webbrowser.open(urls[0])
                self.message = f" Opened {urls[0]}"
            except Exception as ex:  # pragma: no cover
                self.message = f" Could not open a browser: {ex}"
            return None

        keys = {"n": lambda: move(1), "N": lambda: move(-1), "p": lambda: move(-1),
                "a": lambda: record("agrees"), "d": lambda: record("differs"),
                "u": lambda: record("unsure"), "D": open_def, "r": toggle_raw,
                "A": lambda: self.ask(state["entry"]), "L": lambda: self.lean_check(state["entry"]),
                "o": open_link, "?": lambda: self.text_pager("Help", HELP)}
        footer = (" a agrees  d differs  u unsure  D definitions  n/N next/prev  A ask  L lean"
                  "  r LaTeX  o link  ? help  Esc back")
        if self.scr.getmaxyx()[1] < 110:
            footer = " a agree d differ u unsure D defs n/N next A ask ? help Esc back"
        self.pager(lambda: state["entry"].id, lines, keys, footer)

    def sub_detail(self, entry):
        """Detail of an item reached from another item (no list navigation)."""
        saved_rows, saved_sel = self.rows, self.sel
        self.rows = [entry]
        try:
            self.detail(0)
        finally:
            self.rows, self.sel = saved_rows, saved_sel

    # ------------------------------------------------------------------ ask / lean
    def ask(self, e):
        cmd = os.environ.get("CHECK_STATEMENTS_ASK_CMD", "").strip()
        question = self.prompt("Question (Enter: explain the statement; Esc cancels): ")
        if question is None:
            self.message = " Cancelled"
            return None
        context = render.ask_context(self.m, e, question)
        if not cmd:
            fd, path = tempfile.mkstemp(prefix=f"check-{e.id.replace(':', '_')}-", suffix=".md")
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                f.write(context)
            self.text_pager("Ask: no command configured", (
                "CHECK_STATEMENTS_ASK_CMD is not set, so nothing was sent.\n\n"
                f"The context of this item was written to\n  {path}\n\n"
                "To ask an assistant from here, set CHECK_STATEMENTS_ASK_CMD to a shell command "
                "that reads the question and context (Markdown) on its standard input and "
                "writes its answer on its standard output, for example\n\n"
                "  export CHECK_STATEMENTS_ASK_CMD='my-assistant --stdin'\n\n"
                "The command runs in the repository root. The checker shows its output here; it "
                "never records a check by itself."))
            return None
        h, w = self.scr.getmaxyx()
        self.put(h - 1, 0, render.pad(" Asking… (Ctrl-C cancels)", w - 1), "bar")
        self.refresh()
        try:
            p = subprocess.run(cmd, shell=True, input=context, capture_output=True, text=True,
                               cwd=self.m.root)
            out = p.stdout
            if p.returncode != 0:
                out += f"\n\n[the command exited with status {p.returncode}]\n{p.stderr[-2000:]}"
        except KeyboardInterrupt:
            self.message = " Cancelled"
            return None
        self.text_pager(f"Answer about {e.id} (not a check)", out or "(empty answer)")
        return None

    def lean_check(self, e):
        from . import lean_check
        h, w = self.scr.getmaxyx()
        self.put(h - 1, 0, render.pad(" Running lake env lean… (Ctrl-C cancels)", w - 1), "bar")
        self.refresh()
        try:
            out = lean_check.check_types(self.m, [n for n, d in e.decls if d is not None])
        except KeyboardInterrupt:
            self.message = " Cancelled"
            return None
        self.text_pager(f"Lean #check for {e.id}", out)
        return None

    # ------------------------------------------------------------------ progress
    def progress(self):
        def lines(w):
            L = [("Progress per package (checked: latest check current, agrees or differs)", "title"), ("", "text")]
            bw = max(10, w - 62)
            L.append((f"{'package':<11}{'items':>6}{'≥1':>6}{'≥2':>6}{'mine':>6}{'stale':>6}{'differs':>8}  progress", "h"))
            tot = [0] * 6
            for pk in self.m.packages() + ["total"]:
                es = [e for e in self.m.entries if pk == "total" or e.item.package == pk]
                sts = [self.statuses[e.id] for e in es]
                row = [len(es), sum(1 for s in sts if s.n), sum(1 for s in sts if s.n >= 2),
                       sum(1 for s in sts if s.mine is not None and not s.mine_stale),
                       sum(1 for s in sts if s.stale), sum(1 for s in sts if s.differs)]
                frac = row[1] / row[0] if row[0] else 0
                fill = int(round(frac * bw))
                barx = "█" * fill + "░" * (bw - fill)
                L.append((f"{pk:<11}{row[0]:>6}{row[1]:>6}{row[2]:>6}{row[3]:>6}{row[4]:>6}{row[5]:>8}  {barx} {frac:4.0%}",
                          "key" if pk == "total" else "text"))
            L.append(("", "text"))
            L.append(("By priority:", "h"))
            for t, name in TIERS.items():
                es = [e for e in self.m.entries if e.tier == t]
                n = sum(1 for e in es if self.statuses[e.id].n)
                L.append((f"  {name:<36}{len(es):>5} items, {n:>4} checked", "text"))
            return L
        self.pager("Progress", lines)

    # ------------------------------------------------------------------ main loop
    def run(self):
        curses.curs_set(0)
        self.scr.keypad(True)
        while True:
            self.draw_list()
            self.refresh()
            ch = self.scr.get_wch()
            h, w = self.scr.getmaxyx()
            page = max(1, h - 5)
            n = len(self.rows)
            if ch in ("q", "Q"):
                return
            elif ch in (curses.KEY_DOWN, "j"):
                self.sel = min(max(0, n - 1), self.sel + 1)
            elif ch in (curses.KEY_UP, "k"):
                self.sel = max(0, self.sel - 1)
            elif ch == curses.KEY_NPAGE or ch == " ":
                self.sel = min(max(0, n - 1), self.sel + page)
            elif ch == curses.KEY_PPAGE:
                self.sel = max(0, self.sel - page)
            elif ch in (curses.KEY_HOME, "g"):
                self.sel = 0
            elif ch in (curses.KEY_END, "G"):
                self.sel = max(0, n - 1)
            elif ch in ("\n", "\r", curses.KEY_ENTER, curses.KEY_RIGHT, "l"):
                if self.rows:
                    keep = self.rows[self.sel].id
                    self.detail(self.sel)
                    keep = self.rows[self.sel].id if self.rows else keep
                    self.apply(keep=keep)
            elif ch == "/":
                q = self.prompt("Search: ", self.query)
                if q is not None:
                    self.query = q.strip()
                    self.apply()
            elif ch == "\x1b":
                if self.query:
                    self.query = ""
                    self.apply()
            elif ch == "f":
                self.filter = (self.filter + 1) % len(FILTERS)
                self.apply()
            elif ch == "F":
                self.filter = (self.filter - 1) % len(FILTERS)
                self.apply()
            elif isinstance(ch, str) and ch in "123456":
                self.filter = int(ch) - 1
                self.apply()
            elif ch == "p":
                self.pkg = (self.pkg + 1) % len(self.packages())
                self.apply()
            elif ch == "P":
                self.pkg = (self.pkg - 1) % len(self.packages())
                self.apply()
            elif ch == "0":
                self.pkg = 0
                self.apply()
            elif ch == "s":
                keep = self.rows[self.sel].id if self.rows else None
                self.sort = (self.sort + 1) % len(SORTS)
                self.apply(keep=keep)
            elif ch == "t":
                self.progress()
            elif ch == "?":
                self.text_pager("Help", HELP)
            elif ch == curses.KEY_RESIZE:
                pass


def main(model, color=True):
    locale.setlocale(locale.LC_ALL, "")
    os.environ.setdefault("ESCDELAY", "25")

    def run(scr):
        App(scr, model, color=color).run()

    curses.wrapper(run)
