#!/usr/bin/env python3
"""Acceptance check for a fixed-statement run.

  check_spec.py RUN.json [--repo DIR] [--rev REV] [--strict] [--build] [--axioms] [--elaborated]

RUN.json names the pinned baseline commit, the pinned file and declarations, the files the agent
may change, and the parameters below (see runs/*.json). The baseline text is read from the
baseline commit with `git show`, so the baseline commit must be in the history of the checked
repository. By default the working tree of DIR (default: the current repository) is checked;
with `--rev REV` a commit is checked without checking it out (`--build`, `--axioms` and
`--elaborated` then are not available).

Checks, in order:

1. statements: every pinned definition (`defs`) is byte-identical to the baseline as a whole
   (from its keyword line to the first blank line), and every pinned theorem (`theorems`) is
   byte-identical from its keyword line up to its first `:=`. A declaration is found by the first
   line that starts with one of `keywords` (optionally after `noncomputable`) followed by its
   name. If `context` lists line prefixes (for example `variable`, `namespace`, `open `,
   `import`), the lines of the pinned file that start with them must be the same, in the same
   order, as in the baseline; extra lines listed in `reviewed` are reported, not rejected.
   Files in `pinned_files` must be byte-identical.
2. prefixes (the `omit` rule): the command modifiers directly above each pinned theorem (lines
   ending in ` in`, and attributes `@[...]`; comments are skipped) must be those of the baseline,
   except that `omit ... in` and `set_option maxHeartbeats/maxRecDepth/synthInstance.maxHeartbeats
   ... in` lines may be added.
3. banned tokens: no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `axiom`
   declarations, `debug.skipKernelTC` or `Kernel.skip` in the code (before any `--`) of the files
   under `scan` (directories, single files, or glob patterns such as `median/Median/Basic*.lean`).
4. files: every file changed since the baseline commit (tracked or untracked) matches `allowed`.
5. with `--build`: `lake build` succeeds in the package directory, with no warning located in a
   file changed since the baseline (other warnings are listed).
6. with `--axioms`: `#print axioms` of every pinned theorem lists only `propext`,
   `Classical.choice` and `Quot.sound`.
7. with `--elaborated`: every pinned declaration, as Lean elaborates it, is the same as in the
   baseline: the `pp.all` printout (every name fully resolved, every implicit argument shown) of
   the type of each pinned theorem (`#check`) and of each pinned definition (`#print`) is compared
   with the printout obtained by elaborating the baseline version of the pinned file. The baseline
   file is elaborated against the checked tree's versions of the modules it imports. A theorem
   may differ only by instance binders `[...]` removed from its leading binders (what `omit`
   does); everything else must be identical, up to the names Lean generates for instance
   binders (`inst`, `inst_1`, ...), which are compared up to consistent renaming.

`--strict` additionally pins the `variable`, `namespace`, `open ` and `include ` lines of the
pinned file in runs whose `context` does not (the four earliest runs pinned no context lines).

Exit status 0 and `SPEC OK` when nothing is violated, 1 and `SPEC VIOLATED` otherwise.
"""
import argparse
import fnmatch
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

FORBIDDEN = (r"\b(sorry|admit|native_decide|implemented_by|extern)\b"
             r"|^\s*((private|protected|noncomputable|unsafe)\s+)*axiom\s"
             r"|debug\.skipKernelTC|Kernel\.skip")
STRICT_CONTEXT = ["variable", "namespace", "open ", "include "]
ALLOWED_PREFIX = re.compile(r"^(omit\s.*\sin"
                            r"|set_option\s+(maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats)\s+\d+\s+in)$")
AXIOMS_OK = {"propext", "Classical.choice", "Quot.sound"}


def git(repo: Path, *args: str, check: bool = True) -> str:
    r = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, text=True)
    if check and r.returncode:
        sys.exit(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


class Tree:
    """The state being checked: a working tree, or a commit when `rev` is given."""

    def __init__(self, repo: Path, rev: str | None):
        self.repo, self.rev = repo, rev

    def read(self, path: str) -> str | None:
        if self.rev is None:
            p = self.repo / path
            return p.read_text() if p.is_file() else None
        r = subprocess.run(["git", "-C", str(self.repo), "show", f"{self.rev}:{path}"],
                           capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else None

    def lean_files(self, entry: str) -> list[str]:
        if "*" in entry:
            parent = entry.rsplit("/", 1)[0]
            return [f for f in self.lean_files(parent) if fnmatch.fnmatch(f, entry)]
        if entry.endswith(".lean"):
            return [entry] if self.read(entry) is not None else []
        if self.rev is None:
            return sorted(str(p.relative_to(self.repo)) for p in (self.repo / entry).rglob("*.lean"))
        names = git(self.repo, "ls-tree", "-r", "--name-only", self.rev, "--", entry).split()
        return sorted(n for n in names if n.endswith(".lean"))

    def changed(self, base: str) -> list[str]:
        if self.rev is not None:
            return git(self.repo, "diff", "--name-only", base, self.rev).split()
        diff = git(self.repo, "diff", "--name-only", base).split()
        new = git(self.repo, "ls-files", "--others", "--exclude-standard").split()
        return sorted(set(diff) | set(new))


def decl_index(lines: list[str], name: str, keywords: list[str]) -> int | None:
    pat = re.compile(rf"^(noncomputable\s+)?({'|'.join(keywords)})\s+{re.escape(name)}\b")
    return next((k for k, l in enumerate(lines) if pat.match(l)), None)


def decl_text(src: str, name: str, whole: bool, keywords: list[str]) -> str:
    lines = src.split("\n")
    i = decl_index(lines, name, keywords)
    if i is None:
        return "<MISSING>"
    out = []
    for l in lines[i:]:
        if whole:
            if not l.strip():
                break
            out.append(l)
        else:
            out.append(l)
            if ":=" in l:
                out[-1] = l[: l.index(":=")]
                break
    return "\n".join(out).rstrip()


def modifiers(src: str, name: str, keywords: list[str]) -> list[str]:
    """Command modifiers (`... in`, `@[...]`) directly above a declaration, comments skipped."""
    lines = src.split("\n")
    i = decl_index(lines, name, keywords)
    out, k, in_comment = [], (i or 0) - 1, False
    while i is not None and k >= 0:
        s = lines[k].strip()
        if in_comment:
            in_comment = "/-" not in s
        elif s.endswith("-/"):
            in_comment = not s.startswith("/-")
        elif s.startswith("--"):
            pass
        elif s.endswith(" in") or s.startswith("@["):
            out.append(s)
        else:
            break
        k -= 1
    return out[::-1]


def context_lines(src: str, prefixes: list[str]) -> list[str]:
    return [l for l in src.split("\n") if prefixes and l.startswith(tuple(prefixes))]


def check(cfg: dict, repo: Path, tree: Tree, strict: bool) -> list[str]:
    base = Tree(repo, cfg["baseline"])
    problems = []
    old, new = base.read(cfg["file"]), tree.read(cfg["file"])
    if old is None:
        sys.exit(f"{cfg['file']} not found at the baseline commit {cfg['baseline'][:7]}")
    if new is None:
        return [f"MISSING  {cfg['file']}"]
    kw = cfg["keywords"]
    # 1. statements
    for name in cfg["defs"] + cfg["theorems"]:
        whole = name in cfg["defs"]
        a, b = decl_text(old, name, whole, kw), decl_text(new, name, whole, kw)
        if a == "<MISSING>":
            sys.exit(f"{name} not found in the baseline: check the configuration")
        if a != b:
            problems.append(f"CHANGED  {name}\n--- baseline\n{a}\n--- now\n{b}\n")
    ctx = list(cfg["context"])
    if strict:
        ctx += [p for p in STRICT_CONTEXT if p not in ctx]
    a, b = context_lines(old, ctx), context_lines(new, ctx)
    if a != b:
        rest = list(b)
        reviewed = [l for l in cfg.get("reviewed", []) if l in rest and l not in a]
        for l in reviewed:
            rest.remove(l)
        if rest == a:
            for l in reviewed:
                print(f"REVIEWED context line (listed in the run's `reviewed`): {l}")
        else:
            problems.append("CHANGED  <context lines " + ", ".join(repr(p) for p in ctx) + ">\n--- baseline\n"
                            + "\n".join(a) + "\n--- now\n" + "\n".join(b) + "\n")
    for f in cfg.get("pinned_files", []):
        if base.read(f) != tree.read(f):
            problems.append(f"CHANGED  pinned file {f}")
    # 2. prefixes (the omit rule)
    for name in cfg["theorems"]:
        a, b = modifiers(old, name, kw), modifiers(new, name, kw)
        rest = list(b)
        for l in a:
            if l in rest:
                rest.remove(l)
            else:
                problems.append(f"PREFIX   {name}: baseline modifier removed: {l}")
        for l in rest:
            if ALLOWED_PREFIX.match(l):
                print(f"allowed modifier before {name}: {l}")
            else:
                problems.append(f"PREFIX   {name}: modifier added: {l}")
    # 3. banned tokens
    for entry in cfg["scan"]:
        for f in tree.lean_files(entry):
            for k, l in enumerate((tree.read(f) or "").split("\n"), 1):
                if re.search(FORBIDDEN, l.split("--", 1)[0]):
                    problems.append(f"FORBIDDEN {f}:{k}: {l.strip()}")
    # 4. files
    allowed = re.compile(cfg["allowed"])
    for f in tree.changed(cfg["baseline"]):
        if not allowed.match(f):
            problems.append(f"DISALLOWED CHANGE {f}")
    return problems


def lake(pkg: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["lake", *args], cwd=pkg, capture_output=True, text=True)


def build(cfg: dict, repo: Path, tree: Tree) -> list[str]:
    pkg = repo / cfg["package"]
    print(f"lake build in {cfg['package']}/ ...", flush=True)
    r = lake(pkg, "build")
    out = r.stdout + r.stderr
    problems = [] if r.returncode == 0 else [f"BUILD FAILED (exit {r.returncode})\n{out[-4000:]}"]
    changed = set(tree.changed(cfg["baseline"]))
    for m in re.finditer(r"warning: (?:\./)*(\S+?\.lean):(\d+):(\d+): ([^\n]*)", out):
        path = f"{cfg['package']}/{m.group(1)}"
        msg = f"{path}:{m.group(2)}:{m.group(3)}: {m.group(4)}"
        if path in changed:
            problems.append(f"WARNING  {msg}")
        else:
            print(f"warning outside the agent's files: {msg}")
    if r.returncode == 0:
        print("build OK")
    return problems


def axioms(cfg: dict, repo: Path) -> list[str]:
    pkg = repo / cfg["package"]
    module = cfg["file"].split("/", 1)[1].removesuffix(".lean").replace("/", ".")
    r = lake(pkg, "build", module)
    if r.returncode:
        return [f"AXIOMS   cannot build {module}\n{(r.stdout + r.stderr)[-2000:]}"]
    names = [f"{cfg['namespace']}.{t}" for t in cfg["theorems"]]
    with tempfile.TemporaryDirectory() as d:
        audit = Path(d) / "Audit.lean"
        audit.write_text(f"import {module}\n" + "".join(f"#print axioms {n}\n" for n in names))
        r = lake(pkg, "env", "lean", str(audit))
    if r.returncode:
        return [f"AXIOMS   audit failed\n{(r.stdout + r.stderr)[-2000:]}"]
    found = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", r.stdout))
    found.update({n: "" for n in re.findall(r"'([^']+)' does not depend on any axioms", r.stdout)})
    problems = []
    for n in names:
        if n not in found:
            problems.append(f"AXIOMS   no report for {n}")
            continue
        bad = {a.strip() for a in found[n].split(",") if a.strip()} - AXIOMS_OK
        if bad:
            problems.append(f"AXIOMS   {n} depends on {sorted(bad)}")
    if not problems:
        print(f"axioms OK: {len(names)} pinned theorems use only {', '.join(sorted(AXIOMS_OK))}")
    return problems


MARK = "@@decl "


def elaborate(pkg: Path, header: str, names: list[tuple[str, str]]) -> dict[str, str] | str:
    """Elaborate `header` followed by `pp.all` printouts of `names`; return name -> printout."""
    cmds = "".join(f'\n#eval IO.println "{MARK}{n}"\nset_option pp.all true in\n'
                   f"{'#check @' if kind == 'theorem' else '#print '}{n}\n" for kind, n in names)
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "Elaborated.lean"
        f.write_text(header + "\n" + cmds)
        r = lake(pkg, "env", "lean", str(f))
    if r.returncode:
        return (r.stdout + r.stderr)[-3000:]
    out, cur = {}, None
    for line in r.stdout.split("\n"):
        if line.startswith(MARK):
            cur = line[len(MARK):].strip()
            out[cur] = []
        elif cur is not None and not re.match(r"^\S+\.lean:\d+:\d+: warning: declaration uses 'sorry'", line):
            out[cur].append(line)
    return {k: "\n".join(v).strip() for k, v in out.items()}


def rename_instances(s: str) -> str:
    """Rename the auto-generated instance binder names (`inst`, `inst_1`, ...) in order of
    appearance. They are bound variables, so this preserves meaning; dropping an unnamed
    instance binder shifts the numbering of the later ones."""
    names: dict[str, str] = {}
    return re.sub(r"\binst(?:_\d+)?\b", lambda m: names.setdefault(m.group(0), f"inst#{len(names)}"), s)


def split_binders(s: str) -> tuple[list[str], str]:
    """Split `head : ∀ b₁ b₂ …, body` into the binder groups and the rest (whitespace collapsed)."""
    s = re.sub(r"\s+", " ", s).strip()
    head, sep, typ = s.partition(" : ")
    if not typ.startswith("∀ "):
        return [], s
    groups, depth, start, k = [], 0, None, 2
    while k < len(typ):
        c = typ[k]
        if c in "([{⦃":
            if depth == 0:
                start = k
            depth += 1
        elif c in ")]}⦄":
            depth -= 1
            if depth == 0:
                groups.append(typ[start:k + 1])
        elif c == "," and depth == 0:
            return groups, head + sep + typ[k + 1:].strip()
        k += 1
    return [], s


def dropped_instances(old: str, new: str) -> list[str] | None:
    """The instance binders dropped from `old` to get `new`, or None if `new` differs otherwise."""
    ob, orest = split_binders(old)
    nb, nrest = split_binders(new)
    if orest != nrest:
        return None
    dropped, i = [], 0
    for b in ob:
        if i < len(nb) and nb[i] == b:
            i += 1
        elif b.startswith("["):
            dropped.append(b)
        else:
            return None
    return dropped if i == len(nb) else None


def elaborated(cfg: dict, repo: Path) -> list[str]:
    """The pinned declarations, as Lean elaborates them, are the same as in the baseline."""
    pkg = repo / cfg["package"]
    module = cfg["file"].split("/", 1)[1].removesuffix(".lean").replace("/", ".")
    r = lake(pkg, "build", module)
    if r.returncode:
        return [f"ELABORATED cannot build {module}"]
    names = ([("def", f"{cfg['namespace']}.{n}") for n in cfg["defs"]]
             + [("theorem", f"{cfg['namespace']}.{n}") for n in cfg["theorems"]])
    base_src = Tree(repo, cfg["baseline"]).read(cfg["file"])
    old = elaborate(pkg, base_src, names)
    new = elaborate(pkg, f"import {module}", names)
    for label, res in (("baseline", old), ("current", new)):
        if isinstance(res, str):
            return [f"ELABORATED cannot elaborate the {label} declarations\n{res}"]
    problems, generalized = [], 0
    for kind, n in names:
        a, b = old.get(n), new.get(n)
        if a and b:
            a, b = rename_instances(a), rename_instances(b)
        if a and a == b:
            continue
        dropped = dropped_instances(a, b) if a and b and kind == "theorem" else None
        if dropped:
            generalized += 1
            print(f"allowed generalization of {n}: dropped instance argument(s) {' '.join(dropped)}")
        else:
            problems.append(f"ELABORATED {n} differs\n--- baseline\n{a}\n--- now\n{b}\n")
    if not problems:
        print(f"elaborated OK: {len(names)} pinned declarations identical to the baseline (pp.all), "
              f"{generalized} of them up to dropped instance arguments")
    return problems


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("config")
    ap.add_argument("--repo", default=".")
    ap.add_argument("--rev")
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--axioms", action="store_true")
    ap.add_argument("--elaborated", action="store_true")
    a = ap.parse_args()
    if a.rev and (a.build or a.axioms or a.elaborated):
        ap.error("--build, --axioms and --elaborated need a checkout; do not combine them with --rev")
    cfg = json.loads(Path(a.config).read_text())
    repo = Path(git(Path(a.repo), "rev-parse", "--show-toplevel").strip())
    tree = Tree(repo, a.rev)
    print(f"run {cfg['id']}: baseline {cfg['baseline'][:7]}, checking "
          f"{a.rev or 'the working tree'}{' (strict)' if a.strict else ''}")
    problems = check(cfg, repo, tree, a.strict)
    if a.build:
        problems += build(cfg, repo, tree)
    if a.axioms:
        problems += axioms(cfg, repo)
    if a.elaborated:
        problems += elaborated(cfg, repo)
    for p in problems:
        print(p)
    print("SPEC OK" if not problems else f"SPEC VIOLATED ({len(problems)} problem(s))")
    return 0 if not problems else 1


if __name__ == "__main__":
    sys.exit(main())
