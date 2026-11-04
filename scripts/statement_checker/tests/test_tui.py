"""Headless smoke tests of the terminal app, in a pseudo-terminal.

The app writes a text copy of its screen to $CHECK_STATEMENTS_SNAPSHOT after every refresh;
the tests send keys and read these snapshots.
"""
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

from statement_checker.tests import ptydrive

ENTER, ESC, PGDN, DOWN = "\r", "\x1b", "\x1b[6~", "\x1b[B"


@unittest.skipUnless(sys.platform != "win32" and hasattr(os, "fork"), "needs a POSIX pty")
class TestTerminalApp(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.checks = Path(self.tmp.name) / "checks"
        self.env = {"TMPDIR": self.tmp.name, "CHECK_STATEMENTS_ASK_CMD": ""}

    def tearDown(self):
        self.tmp.cleanup()

    def drive(self, keys, cols=80, rows=24, env=None):
        e = dict(self.env)
        e.update(env or {})
        status, snaps, _ = ptydrive.run(
            keys, cols, rows, ["--reviewer", "Test Reviewer", "--checks-dir", str(self.checks)],
            env=e)
        self.assertEqual(status, 0, snaps[-1] if snaps else "no output")
        for s in snaps:
            lines = s.split("\n")
            self.assertLessEqual(len([ln for ln in lines if ln]), rows)
        return snaps

    def records(self):
        out = []
        for p in sorted(self.checks.glob("*.jsonl")):
            out += [json.loads(line) for line in p.read_text().split("\n") if line.strip()]
        return out

    def test_navigation_and_record(self):
        keys = [DOWN, "j", "k", PGDN, "g",                 # move
                "/", *"Theorem 2.1", ENTER,                  # search
                ENTER,                                       # open the detail
                PGDN, "r", "r",                              # scroll, raw toggle
                "d", ENTER,                                  # differs without comment: refused
                *"constants explicit, intended", ENTER,      # the comment
                "D", ESC,                                    # definitions used
                "?", "q",                                    # help
                ESC,                                         # back to the list
                ESC,                                         # clear the search
                "f", "f", "p", "s", "t", ESC, "q"]
        snaps = self.drive(keys)
        joined = "\n".join(snaps)
        self.assertIn("Leanamics statements", snaps[0])
        self.assertIn("★", snaps[0])
        self.assertIn("voter:thm:21", joined)
        self.assertIn("── SOURCE", joined)
        self.assertIn("A comment is required for `differs`", joined)
        self.assertIn("Recorded `differs` for voter:thm:21 as Test Reviewer", joined)
        self.assertIn("Library declarations used by voter:thm:21", joined)
        self.assertIn("DETAIL VIEW", joined)
        self.assertIn("unchecked by me", joined)
        self.assertIn("Progress per package", joined)
        recs = self.records()
        self.assertEqual(len(recs), 1)
        r = recs[0]
        self.assertEqual((r["item"], r["verdict"], r["reviewer"]),
                         ("voter:thm:21", "differs", "Test Reviewer"))
        self.assertEqual(r["comment"], "constants explicit, intended")
        self.assertTrue((self.checks / "test-reviewer.jsonl").is_file())

    def test_cancel_records_nothing(self):
        snaps = self.drive([ENTER, "a", ESC, "u", ESC, ESC, "q"])
        self.assertIn("Cancelled, nothing recorded", "\n".join(snaps))
        self.assertEqual(self.records(), [])

    def test_wide_terminal(self):
        snaps = self.drive([ENTER, ESC, "q"], cols=160, rows=50)
        first = snaps[0]
        # the wide list also shows the Lean names
        self.assertIn("theorem_3_8, theorem_3_8_bigO", first)
        self.assertGreater(len([ln for ln in first.split("\n") if ln.strip()]), 40)

    def test_ask_without_command(self):
        snaps = self.drive([ENTER, "A", *"why?", ENTER, ESC, ESC, "q"])
        self.assertIn("CHECK_STATEMENTS_ASK_CMD is not set", "\n".join(snaps))
        written = list(Path(self.tmp.name).glob("check-voter_thm_21-*.md"))
        self.assertEqual(len(written), 1)
        self.assertIn("why?", written[0].read_text())

    def test_ask_with_command(self):
        cmd = (f"{sys.executable} -c \"import sys; d = sys.stdin.read(); "
               f"print('ANSWER', 'Lean declarations' in d, 'why?' in d)\"")
        snaps = self.drive([ENTER, "A", *"why?", ENTER, ESC, ESC, "q"],
                           env={"CHECK_STATEMENTS_ASK_CMD": cmd})
        self.assertIn("ANSWER True True", "\n".join(snaps))
        self.assertEqual(self.records(), [])


if __name__ == "__main__":
    unittest.main()
