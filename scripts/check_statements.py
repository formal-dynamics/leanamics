#!/usr/bin/env python3
"""Check the Lean statements of Leanamics against their sources.

    python3 scripts/check_statements.py --next        # the next unchecked item
    python3 scripts/check_statements.py --show ID     # its source next to its Lean statement
    python3 scripts/check_statements.py --record ID --verdict agrees --basis transcription
    python3 scripts/check_statements.py --report      # Markdown summary of the checks
    python3 scripts/check_statements.py --validate    # for CI: non-zero exit on error
    python3 scripts/check_statements.py --help

See verification/README.md for what a check means.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from statement_checker.cli import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main())
