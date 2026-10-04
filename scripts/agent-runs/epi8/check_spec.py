#!/usr/bin/env python3
"""Spec gate for the fixed-statement protocol.

  check_spec.py snapshot <worktree> <baseline.json>   # record the pinned baseline
  check_spec.py check    <worktree> <baseline.json>   # verify; prints SPEC OK on success

Checks: frozen files byte-identical; in pinned files every pinned statement (from the
`theorem`/`lemma` keyword up to its `:=`) and every namespace/open/variable/section/end line
is byte-identical and in the same order; no sorry/admit/axiom/opaque/implemented_by/extern/
native_decide in any .lean file under the watched dirs. Added `import` lines are allowed but
reported.
"""
import json, re, sys, pathlib

FROZEN = ["epidemics/Epidemics/Revisited/Defs.lean"]
PINNED = ["epidemics/Epidemics/Revisited/Growth.lean"]
WATCH = ["epidemics/Epidemics", "epidemics/Epidemics.lean"]
HEADER = re.compile(r"^(namespace|open|variable|section|end|noncomputable section|universe)\b")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+(\S+)", re.M)
FORBID = re.compile(r"\b(sorry|admit|axiom|opaque|implemented_by|extern|native_decide)\b")

def strip_comments(src):
    src = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), src, flags=re.S)
    return re.sub(r"--[^\n]*", "", src)

def statements(src):
    out = {}
    for m in DECL.finditer(src):
        end = src.find(":=", m.end())
        out[m.group(2)] = src[m.start():end].rstrip()
    return out

def snapshot(wt):
    data = {"frozen": {}, "pinned": {}}
    for f in FROZEN:
        data["frozen"][f] = (wt / f).read_text()
    for f in PINNED:
        src = (wt / f).read_text()
        data["pinned"][f] = {
            "headers": [l for l in src.splitlines() if HEADER.match(l)],
            "statements": statements(src),
            "imports": [l for l in src.splitlines() if l.startswith("import ")],
        }
    return data

def check(wt, base):
    ok = True
    for f, txt in base["frozen"].items():
        if (wt / f).read_text() != txt:
            print(f"FAIL frozen file changed: {f}"); ok = False
    for f, b in base["pinned"].items():
        src = (wt / f).read_text()
        hdr = [l for l in src.splitlines() if HEADER.match(l)]
        if hdr != b["headers"]:
            print(f"FAIL header lines changed in {f}:\n  was {b['headers']}\n  now {hdr}"); ok = False
        st = statements(src)
        for name, s in b["statements"].items():
            if st.get(name) != s:
                print(f"FAIL statement of {name} changed or missing in {f}"); ok = False
        imps = [l for l in src.splitlines() if l.startswith("import ")]
        for l in imps:
            if l not in b["imports"]:
                print(f"NOTE added import in {f}: {l}")
    files = []
    for w in WATCH:
        p = wt / w
        files += [p] if p.is_file() else sorted(p.rglob("*.lean"))
    for p in files:
        for i, line in enumerate(strip_comments(p.read_text()).splitlines(), 1):
            if FORBID.search(line):
                print(f"FAIL forbidden token at {p.relative_to(wt)}:{i}: {line.strip()}"); ok = False
    print("SPEC OK" if ok else "SPEC FAILED")
    return ok

if __name__ == "__main__":
    mode, wt, bj = sys.argv[1], pathlib.Path(sys.argv[2]).resolve(), pathlib.Path(sys.argv[3])
    if mode == "snapshot":
        bj.write_text(json.dumps(snapshot(wt), indent=1)); print(f"baseline written to {bj}")
    else:
        sys.exit(0 if check(wt, json.loads(bj.read_text())) else 1)
