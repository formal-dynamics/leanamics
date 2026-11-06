#!/usr/bin/env python3
"""Run the tests of the statement checker."""
import sys
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(SCRIPTS))

if __name__ == "__main__":
    suite = unittest.defaultTestLoader.discover(str(SCRIPTS / "statement_checker" / "tests"),
                                                top_level_dir=str(SCRIPTS))
    result = unittest.TextTestRunner(verbosity=1 if "-q" in sys.argv else 2).run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
