"""Make blueprint LaTeX readable in a terminal: common macros and math to Unicode.

The rendering is best effort and only for display; hashes are computed on the LaTeX source.
Unknown macros are kept as they are written.
"""
import re
import unicodedata

SYMBOLS = {
    # Greek
    "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ϵ", "varepsilon": "ε",
    "zeta": "ζ", "eta": "η", "theta": "θ", "vartheta": "ϑ", "iota": "ι", "kappa": "κ",
    "lambda": "λ", "mu": "μ", "nu": "ν", "xi": "ξ", "pi": "π", "varpi": "ϖ", "rho": "ρ",
    "varrho": "ϱ", "sigma": "σ", "varsigma": "ς", "tau": "τ", "upsilon": "υ", "phi": "ϕ",
    "varphi": "φ", "chi": "χ", "psi": "ψ", "omega": "ω",
    "Gamma": "Γ", "Delta": "Δ", "Theta": "Θ", "Lambda": "Λ", "Xi": "Ξ", "Pi": "Π",
    "Sigma": "Σ", "Upsilon": "Υ", "Phi": "Φ", "Psi": "Ψ", "Omega": "Ω",
    # relations and operators
    "le": "≤", "leq": "≤", "ge": "≥", "geq": "≥", "leqslant": "≤", "geqslant": "≥",
    "nleq": "≰", "ngeq": "≱", "leqq": "≦", "geqq": "≧", "ne": "≠", "neq": "≠", "lt": "<", "gt": ">",
    "approx": "≈", "sim": "∼", "simeq": "≃", "equiv": "≡", "cong": "≅", "propto": "∝",
    "ll": "≪", "gg": "≫", "lesssim": "≲", "gtrsim": "≳", "preceq": "⪯", "succeq": "⪰",
    "prec": "≺", "succ": "≻", "in": "∈", "notin": "∉", "ni": "∋", "subset": "⊂",
    "subseteq": "⊆", "supset": "⊃", "supseteq": "⊇", "cup": "∪", "cap": "∩",
    "setminus": "∖", "smallsetminus": "∖", "emptyset": "∅", "varnothing": "∅",
    "times": "×", "cdot": "·", "circ": "∘", "pm": "±", "mp": "∓", "div": "÷", "ast": "∗",
    "star": "⋆", "oplus": "⊕", "otimes": "⊗", "bigotimes": "⨂", "bigoplus": "⨁",
    "to": "→", "rightarrow": "→", "leftarrow": "←", "gets": "←", "mapsto": "↦",
    "Rightarrow": "⇒", "Leftarrow": "⇐", "Leftrightarrow": "⇔", "iff": "⇔", "implies": "⇒",
    "leftrightarrow": "↔", "longrightarrow": "⟶", "longmapsto": "⟼", "uparrow": "↑",
    "downarrow": "↓", "hookrightarrow": "↪",
    "forall": "∀", "exists": "∃", "nexists": "∄", "neg": "¬", "lnot": "¬", "land": "∧",
    "wedge": "∧", "lor": "∨", "vee": "∨", "top": "⊤", "bot": "⊥", "perp": "⊥",
    "parallel": "∥", "mid": "∣", "nmid": "∤", "infty": "∞", "partial": "∂", "nabla": "∇",
    "sum": "∑", "prod": "∏", "coprod": "∐", "int": "∫", "oint": "∮", "bigcup": "⋃",
    "bigcap": "⋂", "bigvee": "⋁", "bigwedge": "⋀", "sqcup": "⊔",
    "langle": "⟨", "rangle": "⟩", "lceil": "⌈", "rceil": "⌉", "lfloor": "⌊", "rfloor": "⌋",
    "lvert": "|", "rvert": "|", "vert": "|", "Vert": "‖", "lVert": "‖", "rVert": "‖",
    "|": "‖", "ldots": "…", "dots": "…", "cdots": "⋯", "vdots": "⋮", "ddots": "⋱",
    "dotsc": "…", "dotsb": "⋯", "ell": "ℓ", "hbar": "ℏ", "Re": "ℜ", "Im": "ℑ", "aleph": "ℵ",
    "prime": "′", "angle": "∠", "triangle": "△", "Box": "□", "square": "□", "dagger": "†",
    "S": "§", "P": "¶", "colon": ":", "triangleq": "≜", "coloneqq": "≔", "models": "⊨",
    "vdash": "⊢", "bullet": "•", "checkmark": "✓", "wp": "℘",
    "E": "𝔼", "Pr": "ℙ", "N": "ℕ", "R": "ℝ", "Z": "ℤ", "Q": "ℚ", "C": "ℂ",
    # text-mode
    "ldots": "…", "textendash": "–", "textemdash": "—", "textbackslash": "\\",
    "%": "%", "&": "&", "#": "#", "_": "_", "{": "{", "}": "}", "$": "$",
    "quad": "  ", "qquad": "    ", ",": " ", ";": " ", ":": " ", "!": "", " ": " ",
    "noindent": "", "par": "\n\n", "newline": "\n", "\\": "\n", "displaystyle": "",
    "textstyle": "", "scriptstyle": "", "left": "", "right": "", "big": "", "Big": "",
    "bigg": "", "Bigg": "", "bigl": "", "bigr": "", "Bigl": "", "Bigr": "", "biggl": "",
    "biggr": "", "Biggl": "", "Biggr": "", "bigm": "", "Bigm": "", "middle": "",
    "nonumber": "", "notag": "", "limits": "", "nolimits": "", "relax": "", "protect": "",
    "smallskip": "", "medskip": "", "bigskip": "", "item": "\n • ", "centering": "",
}
OPERATORS = {"log", "ln", "exp", "min", "max", "sup", "inf", "lim", "liminf", "limsup", "deg",
             "det", "dim", "ker", "gcd", "Pr", "arg", "sin", "cos", "tan", "cosh", "sinh",
             "tanh", "mod", "bmod", "argmin", "argmax", "Var", "poly", "polylog", "diam",
             "dist", "supp", "rank", "tr", "sgn", "sign"}
BLACKBOARD = {c: chr(0x1D538 + i) for i, c in enumerate("ABCDEFGHIJKLMNOPQRSTUVWXYZ")}
BLACKBOARD.update({"C": "ℂ", "H": "ℍ", "N": "ℕ", "P": "ℙ", "Q": "ℚ", "R": "ℝ", "Z": "ℤ",
                   "E": "𝔼", "1": "𝟙"})
CALLIGRAPHIC = {"A": "𝒜", "B": "ℬ", "C": "𝒞", "D": "𝒟", "E": "ℰ", "F": "ℱ", "G": "𝒢",
                "H": "ℋ", "I": "ℐ", "J": "𝒥", "K": "𝒦", "L": "ℒ", "M": "ℳ", "N": "𝒩",
                "O": "𝒪", "P": "𝒫", "Q": "𝒬", "R": "ℛ", "S": "𝒮", "T": "𝒯", "U": "𝒰",
                "V": "𝒱", "W": "𝒲", "X": "𝒳", "Y": "𝒴", "Z": "𝒵"}
SUPER = dict(zip("0123456789+-=()niatkjrmxpTdse/lbc*", "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁿⁱᵃᵗᵏʲʳᵐˣᵖᵀᵈˢᵉᐟˡᵇᶜ*"))
SUPER.update({"−": "⁻", "′": "′", "T": "ᵀ", "δ": "ᵟ", "ε": "ᵋ", "θ": "ᶿ", "·": "˙"})
SUB = dict(zip("0123456789+-=()aeoxhklmnpstijruv", "₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₒₓₕₖₗₘₙₚₛₜᵢⱼᵣᵤᵥ"))
SUB.update({"−": "₋", "β": "ᵦ", "γ": "ᵧ", "ρ": "ᵨ", "φ": "ᵩ", "χ": "ᵪ"})
ACCENTS = {"bar": "\u0304", "overline": "\u0305", "hat": "\u0302", "widehat": "\u0302",
           "tilde": "\u0303", "widetilde": "\u0303", "vec": "\u20d7", "dot": "\u0307",
           "ddot": "\u0308", "check": "\u030c"}
TEXT_ACCENTS = {"'": "\u0301", "`": "\u0300", "^": "\u0302", '"': "\u0308", "~": "\u0303",
                "H": "\u030b", "v": "\u030c", "c": "\u0327", "u": "\u0306", "=": "\u0304",
                ".": "\u0307", "k": "\u0328", "r": "\u030a"}
STYLE_KEEP = {"emph", "textit", "textbf", "textrm", "textsf", "text", "mathrm", "mathit",
              "mathsf", "operatorname", "mbox", "hbox", "textnormal", "textup", "mathbf",
              "boldsymbol", "bm", "textsc", "underline", "mathnormal", "ensuremath", "fbox"}
STYLE_CODE = {"texttt", "mathtt", "code", "verb", "lstinline"}
DROP_ARG = {"label", "index", "vspace", "hspace", "phantom", "vphantom", "hphantom", "leanok",
            "uses", "lean", "notready", "mathlibok"}


def _group(s, i):
    """Read a braced group or a single token starting at s[i] (after spaces).

    Returns (content, next index)."""
    n = len(s)
    while i < n and s[i] in " \t":
        i += 1
    if i >= n:
        return "", i
    if s[i] == "{":
        depth, j = 0, i
        while j < n:
            c = s[j]
            if c == "\\":
                j += 2
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    return s[i + 1:j], j + 1
            j += 1
        return s[i + 1:], n
    if s[i] == "\\":
        m = re.match(r"\\([A-Za-z]+|.)", s[i:])
        return m.group(0), i + len(m.group(0))
    return s[i], i + 1


def _optional(s, i):
    """Skip an optional argument [ ... ] at s[i] (after spaces); return (content, index)."""
    j = i
    while j < len(s) and s[j] == " ":
        j += 1
    if j < len(s) and s[j] == "[":
        depth, k = 0, j
        while k < len(s):
            if s[k] == "[":
                depth += 1
            elif s[k] == "]":
                depth -= 1
                if depth == 0:
                    return s[j + 1:k], k + 1
            k += 1
    return None, i


def _script(text, table):
    """Map text to super/subscript characters if every character has one."""
    t = text.replace(" ", "")
    if t and all(c in table for c in t):
        return "".join(table[c] for c in t)
    return None


def _simple(x):
    return re.fullmatch(r"[\w.′]+|[\w.]+\([\w.,]*\)|\S", x) is not None


def render(tex, code=lambda s: s):
    """Render a LaTeX fragment as Unicode text. `code` wraps \\texttt arguments."""
    out = _render(tex, code)
    out = out.replace("---", "—").replace("--", "–").replace("``", "“").replace("''", "”")
    out = re.sub(r"[ \t]+", " ", out)
    out = re.sub(r" *\n *", "\n", out)
    out = re.sub(r"\n{3,}", "\n\n", out)
    out = re.sub(r"([⌈⌊⟨]) +", r"\1", out)
    out = re.sub(r" +([⌉⌋⟩])", r"\1", out)
    return unicodedata.normalize("NFC", out.strip())


def _render(s, code):
    out = []
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c == "\\":
            m = re.match(r"\\([A-Za-z]+)\*?|\\(.)", s[i:], re.S)
            if m is None:  # a trailing backslash
                i += 1
                continue
            name = m.group(1) or m.group(2)
            i += len(m.group(0))
            if name in ("[", "]"):
                out.append("\n    " if name == "[" else "\n")
            elif name in ("(", ")"):
                pass
            elif (m.group(2) is not None and name in TEXT_ACCENTS) or (
                    name in ("H", "v", "c", "u", "k", "r") and s[i:i + 1] == "{"):
                arg, i = _group(s, i)
                inner = _render(arg, code)
                out.append(inner[:1] + TEXT_ACCENTS[name] + inner[1:] if inner else "")
            elif name in ("frac", "tfrac", "dfrac", "cfrac"):
                a, i = _group(s, i)
                b, i = _group(s, i)
                ra, rb = _render(a, code).strip(), _render(b, code).strip()
                ra = ra if _simple(ra) else f"({ra})"
                rb = rb if _simple(rb) else f"({rb})"
                out.append(f"{ra}/{rb}")
            elif name == "binom" or name == "tbinom" or name == "dbinom":
                a, i = _group(s, i)
                b, i = _group(s, i)
                out.append(f"C({_render(a, code)}, {_render(b, code)})")
            elif name == "sqrt":
                opt, i = _optional(s, i)
                a, i = _group(s, i)
                ra = _render(a, code).strip()
                root = {"3": "∛", "4": "∜"}.get(opt.strip() if opt else "", "√")
                if opt and opt.strip() not in ("3", "4"):
                    root = (_script(opt, SUPER) or f"({opt})") + "√"
                out.append(root + (ra if _simple(ra) else f"({ra})"))
            elif name in ("mathbb", "mathds", "mathbbm"):
                a, i = _group(s, i)
                out.append("".join(BLACKBOARD.get(ch, ch) for ch in a))
            elif name in ("mathcal", "mathscr"):
                a, i = _group(s, i)
                out.append("".join(CALLIGRAPHIC.get(ch, ch) for ch in a))
            elif name == "mathfrak":
                a, i = _group(s, i)
                out.append(a)
            elif name in ACCENTS:
                a, i = _group(s, i)
                ra = _render(a, code)
                if len(ra) == 1:
                    out.append(ra + ACCENTS[name])
                else:
                    out.append(f"{name}({ra})")
            elif name in STYLE_KEEP:
                a, i = _group(s, i)
                out.append(_render(a, code))
            elif name in STYLE_CODE:
                a, i = _group(s, i)
                out.append(code(a.replace("\\_", "_")))
            elif name == "texorpdfstring":
                a, i = _group(s, i)
                _, i = _group(s, i)
                out.append(_render(a, code))
            elif name == "href":
                url, i = _group(s, i)
                a, i = _group(s, i)
                out.append(f"{_render(a, code)} <{url}>")
            elif name == "url":
                url, i = _group(s, i)
                out.append(f"<{url}>")
            elif name in ("ref", "eqref", "autoref", "cref", "Cref"):
                a, i = _group(s, i)
                out.append(f"[{a}]")
            elif name in ("cite", "citep", "citet"):
                opt, i = _optional(s, i)
                a, i = _group(s, i)
                out.append(f"[{a}{', ' + opt if opt else ''}]")
            elif name in DROP_ARG:
                if s[i:i + 1] == "{":
                    _, i = _group(s, i)
            elif name in ("begin", "end"):
                env, i = _group(s, i)
                if env in ("itemize", "enumerate", "description"):
                    out.append("\n")
                elif env in ("equation", "equation*", "align", "align*", "gather", "gather*",
                             "multline", "multline*", "displaymath", "eqnarray", "eqnarray*"):
                    out.append("\n    " if name == "begin" else "\n")
                elif env in ("cases", "aligned", "array", "pmatrix", "bmatrix", "matrix"):
                    if name == "begin" and env == "array":
                        _, i = _group(s, i)
                    out.append("{ " if name == "begin" and env == "cases" else "")
            elif name in ("operatorname",):
                a, i = _group(s, i)
                out.append(a)
            elif name in OPERATORS:
                if out and (out[-1][-1:].isalnum() or out[-1][-1:] == ")"):
                    out.append(" ")
                out.append(name if name != "Pr" else "ℙ")
                if name not in ("Pr",) and s[i:i + 1].isalnum():
                    out.append(" ")
            elif name in ("not",):
                a, i = _group(s, i)
                ra = _render(a, code)
                out.append({"=": "≠", "∈": "∉", "⊆": "⊈", "≤": "≰"}.get(ra.strip(), ra + "\u0338"))
            elif name == "ceil" or name == "floor":
                a, i = _group(s, i)
                l, r = ("⌈", "⌉") if name == "ceil" else ("⌊", "⌋")
                out.append(l + _render(a, code) + r)
            elif name in ("pmod",):
                a, i = _group(s, i)
                out.append(f" (mod {_render(a, code)})")
            elif name in ("section", "subsection", "paragraph", "subsubsection"):
                a, i = _group(s, i)
                out.append(_render(a, code))
            elif name in SYMBOLS:
                out.append(SYMBOLS[name])
                if m.group(1) and SYMBOLS[name] and SYMBOLS[name][-1].isalpha() and s[i:i + 1].isalnum():
                    out.append(" ")
            else:
                # unknown macro: keep it as source, with its braced arguments
                out.append("\\" + name)
                while s[i:i + 1] == "{":
                    a, i = _group(s, i)
                    out.append("{" + _render(a, code) + "}")
        elif c == "$":
            i += 2 if s.startswith("$$", i) else 1
        elif c in "^_":
            a, j = _group(s, i + 1)
            ra = _render(a, code) if a.startswith("\\") or len(a) > 1 else a
            mapped = _script(ra, SUPER if c == "^" else SUB)
            if mapped is not None:
                out.append(mapped)
            elif len(ra) == 1:
                out.append(c + ra + (" " if s[j:j + 1].isalnum() else ""))
            else:
                out.append(c + "{" + ra + "}")
            i = j
        elif c == "~":
            out.append(" ")
            i += 1
        elif c == "{" or c == "}":
            i += 1
        elif c == "\n":
            # single newlines are spaces, blank lines are paragraphs
            if s.startswith("\n\n", i) or (i + 1 < n and s[i + 1:].lstrip(" \t").startswith("\n")):
                out.append("\n\n")
                while i < n and s[i] in "\n \t":
                    i += 1
                continue
            out.append(" ")
            i += 1
        elif c == "&":
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)
