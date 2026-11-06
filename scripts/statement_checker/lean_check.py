"""Optional cross-check of the text extraction: ask Lean for the elaborated types.

For each package, a temporary file imports the modules that define the names and runs
`#check @name`; it is compiled with `lake env lean` in the package directory, so the package
must be built. Nothing else in the checker depends on this.
"""
import os
import subprocess
import tempfile
from pathlib import Path


def module_of(path):
    """`voter/Voter/Model.lean` -> `Voter.Model`."""
    parts = Path(path).with_suffix("").parts[1:]
    return ".".join(parts)


def check_types(model, names, timeout=900):
    """The output of `#check @name` for each name, grouped by package, as text."""
    groups = {}
    for n in names:
        d = model.index.get(n)
        if d is None:
            continue
        groups.setdefault(d.package, []).append((n, d))
    out = []
    for pkg, decls in groups.items():
        mods = sorted({module_of(d.path) for _, d in decls})
        src = "\n".join(f"import {m}" for m in mods) + "\n\nset_option pp.all false\n" + \
            "set_option pp.proofs false\n\n" + \
            "\n".join(f"#check @{n}" for n, _ in decls) + "\n"
        fd, path = tempfile.mkstemp(prefix="check_statements_", suffix=".lean")
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(src)
        try:
            p = subprocess.run(["lake", "env", "lean", path], cwd=model.root / pkg,
                               capture_output=True, text=True, timeout=timeout)
            text = (p.stdout + p.stderr).replace(path, "<check>")
            out.append(f"== {pkg} (lake env lean, exit {p.returncode})\n{text.strip()}\n")
        except FileNotFoundError:
            out.append(f"== {pkg}: `lake` not found on PATH\n")
        except subprocess.TimeoutExpired:
            out.append(f"== {pkg}: timed out after {timeout} s\n")
        finally:
            os.unlink(path)
    return "\n".join(out) if out else "No declaration of the library to check."
