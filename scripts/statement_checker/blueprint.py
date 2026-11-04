"""Parse the leanblueprint sources (`*/blueprint/src/content.tex`) into items.

An item is a theorem-like environment (definition, theorem, lemma, corollary, proposition,
remark) whose body names Lean declarations with `\\lean{A,B,...}`. Its id is
`<package>:<label>`; blueprint labels are stable (the repository rules forbid renaming them).
"""
import re
from dataclasses import dataclass, field

ENVS = ("definition", "theorem", "lemma", "corollary", "proposition", "remark")
SECTIONING = re.compile(r"\\(section|subsection|subsubsection)\*?\s*\{")


@dataclass
class Item:
    package: str
    label: str
    env: str               # definition, theorem, lemma, ...
    title: str             # the optional argument of the environment (LaTeX)
    lean: list             # fully qualified Lean names, in blueprint order
    uses: list             # labels from \uses{...}
    statement: str         # the body without \label, \lean, \uses, \leanok (LaTeX)
    path: str              # repository-relative path of content.tex
    line: int              # 1-based line of \begin{env}
    section: str = ""      # title of the enclosing (sub)section (LaTeX)
    section_intro: str = ""  # text between the section heading and its first environment
    leanok: bool = False
    proof_uses: list = field(default_factory=list)

    @property
    def id(self):
        return f"{self.package}:{self.label}"


def strip_comments(tex):
    """Remove LaTeX comments (an unescaped `%` to the end of the line), keeping line breaks."""
    out = []
    for line in tex.split("\n"):
        i = 0
        while True:
            j = line.find("%", i)
            if j < 0:
                break
            # count the backslashes before the percent sign
            k = j
            while k > 0 and line[k - 1] == "\\":
                k -= 1
            if (j - k) % 2 == 0:
                line = line[:j]
                break
            i = j + 1
        out.append(line)
    return "\n".join(out)


def read_group(text, i, open_ch="{", close_ch="}"):
    """Given `text[i]` is `{` or `[`, return (content, index after the matching bracket).

    Braces nest; inside `[...]` only a `]` outside braces closes. Escaped characters
    (`\\{`, `\\]`) do not count."""
    opener = text[i]
    assert opener in "{[", text[i:i + 20]
    brace = 0
    j = i + 1 if opener == "[" else i
    while j < len(text):
        c = text[j]
        if c == "\\":
            j += 2
            continue
        if c == "{":
            brace += 1
        elif c == "}":
            brace -= 1
            if opener == "{" and brace == 0:
                return text[i + 1:j], j + 1
        elif c == "]" and opener == "[" and brace == 0:
            return text[i + 1:j], j + 1
        j += 1
    raise ValueError(f"unbalanced group at offset {i}")


def _command_args(body, name):
    """All arguments of `\\name{...}` in body, and the body with those commands removed."""
    args, out, i = [], [], 0
    pat = re.compile(r"\\" + name + r"(?![A-Za-z])\s*")
    while True:
        m = pat.search(body, i)
        if not m:
            out.append(body[i:])
            break
        out.append(body[i:m.start()])
        if m.end() < len(body) and body[m.end()] == "{":
            arg, j = read_group(body, m.end())
            args.append(arg)
            i = j
        else:  # a bare \leanok and friends
            args.append(None)
            i = m.end()
    return args, "".join(out)


def split_names(arg):
    return [n.strip() for n in arg.replace("\n", " ").split(",") if n.strip()]


def _line_of(text, offset):
    return text.count("\n", 0, offset) + 1


def parse(tex, package, path):
    """The items of one blueprint file."""
    text = strip_comments(tex)
    items = []
    # positions of sectioning commands, to attach section titles
    sections = []
    for m in SECTIONING.finditer(text):
        title, end = read_group(text, m.end() - 1)
        sections.append((m.start(), end, title))
    env_pat = re.compile(r"\\begin\{(" + "|".join(ENVS) + r")\}")
    i = 0
    while True:
        m = env_pat.search(text, i)
        if not m:
            break
        env = m.group(1)
        j = m.end()
        title = ""
        k = j
        while k < len(text) and text[k] in " \t":
            k += 1
        if k < len(text) and text[k] == "[":
            title, j = read_group(text, k)
        end_tag = "\\end{" + env + "}"
        e = text.find(end_tag, j)
        if e < 0:
            raise ValueError(f"{path}:{_line_of(text, m.start())}: no {end_tag}")
        body = text[j:e]
        i = e + len(end_tag)
        lean_args, rest = _command_args(body, "lean")
        if not lean_args:
            continue
        labels, rest = _command_args(rest, "label")
        uses, rest = _command_args(rest, "uses")
        leanok, rest = _command_args(rest, "leanok")
        _, rest = _command_args(rest, "notready")
        _, rest = _command_args(rest, "mathlibok")
        names = [n for a in lean_args if a for n in split_names(a)]
        label = labels[0].strip() if labels and labels[0] else f"line{_line_of(text, m.start())}"
        sec_title, sec_intro = "", ""
        for (s0, s1, t) in sections:
            if s0 < m.start():
                sec_title = t
                nxt = env_pat.search(text, s1)
                stop = nxt.start() if nxt else len(text)
                sec_intro = text[s1:stop]
        # the proof that directly follows
        proof_uses = []
        pm = re.match(r"\s*\\begin\{proof\}", text[i:])
        if pm:
            pe = text.find("\\end{proof}", i)
            if pe > 0:
                pu, _ = _command_args(text[i:pe], "uses")
                proof_uses = [n for a in pu if a for n in split_names(a)]
        items.append(Item(
            package=package, label=label, env=env, title=" ".join(title.split()),
            lean=names, uses=[n for a in uses if a for n in split_names(a)],
            statement=_tidy(rest), path=path, line=_line_of(text, m.start()),
            section=" ".join(sec_title.split()), section_intro=_tidy(_drop_labels(sec_intro)),
            leanok=bool(leanok), proof_uses=proof_uses))
    return items


def _drop_labels(s):
    return re.sub(r"\\label\{[^}]*\}", "", s)


def _tidy(s):
    """Strip each line and drop leading/trailing blank lines, keeping paragraph breaks."""
    lines = [ln.strip() for ln in s.strip("\n").split("\n")]
    out = []
    for ln in lines:
        if ln or (out and out[-1]):
            out.append(ln)
    while out and not out[-1]:
        out.pop()
    return "\n".join(out)


def abstract(tex):
    """The text of the `abstract` environment, or ''."""
    text = strip_comments(tex)
    m = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", text, re.S)
    return _tidy(m.group(1)) if m else ""
