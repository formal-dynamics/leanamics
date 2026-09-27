#!/usr/bin/env python3
"""Check an Audit.lean file and reject axioms outside Lean's standard foundation."""
import re
import subprocess
import sys
from pathlib import Path

result = subprocess.run(["lake", "env", "lean", "Audit.lean"], text=True, capture_output=True)
print(result.stdout, end="")
print(result.stderr, end="", file=sys.stderr)
if result.returncode:
    sys.exit(result.returncode)
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
empty_reports = re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)
expected = set(re.findall(r"^#print axioms (\S+)\s*$", Path("Audit.lean").read_text(), re.M))
reported = {name for name, _ in reports} | set(empty_reports)
if not expected or reported != expected:
    sys.exit(f"Axiom report mismatch: missing={expected - reported}, unexpected={reported - expected}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for declaration, axioms in reports:
    unexpected = {a.strip() for a in axioms.split(",") if a.strip()} - allowed
    if unexpected:
        sys.exit(f"Unexpected axioms in {declaration}: {sorted(unexpected)}")
print(f"Checked {len(reported)} declarations: only standard Lean axioms.")
