import glob
import re
import unittest
from pathlib import Path

from statement_checker import blueprint
from statement_checker.tests import ROOT

SAMPLE = r"""
\section{Model}\label{sec:model}
Intro text citing arXiv:1310.2858.
% \begin{theorem}[commented]\label{thm:no}\lean{Not.this}\end{theorem}
\begin{definition}[Steps, $x_{[1]}$ and \texttt{f}]\label{def:step}
\lean{A.step,
  A.run}\leanok\uses{def:base}
A step 100\% of the time; % a comment \lean{Not.this}
see Lemma~\ref{lem:x}.
\end{definition}
\begin{proof}\leanok\uses{lem:proofonly}
trivial
\end{proof}
\subsection{No lean}
\begin{lemma}[Informal]\label{lem:informal}
No Lean here.
\end{lemma}
\begin{theorem}\label{thm:t}\lean{A.t}
Statement.
\end{theorem}
"""


class TestParser(unittest.TestCase):
    def test_sample(self):
        items = blueprint.parse(SAMPLE, "pkg", "pkg/blueprint/src/content.tex")
        self.assertEqual([i.id for i in items], ["pkg:def:step", "pkg:thm:t"])
        d = items[0]
        self.assertEqual(d.env, "definition")
        self.assertEqual(d.title, r"Steps, $x_{[1]}$ and \texttt{f}")
        self.assertEqual(d.lean, ["A.step", "A.run"])
        self.assertEqual(d.uses, ["def:base"])
        self.assertTrue(d.leanok)
        self.assertEqual(d.proof_uses, ["lem:proofonly"])
        self.assertIn(r"100\% of the time;", d.statement)
        self.assertNotIn("Not.this", d.statement)
        self.assertNotIn("\\lean", d.statement)
        self.assertEqual(d.section, "Model")
        self.assertEqual(d.line, 5)
        t = items[1]
        self.assertEqual(t.title, "")
        self.assertEqual(t.section, "No lean")
        self.assertFalse(t.leanok)

    def test_strip_comments(self):
        self.assertEqual(blueprint.strip_comments("a\\% b % c\nd"), "a\\% b \nd")
        self.assertEqual(blueprint.strip_comments("a\\\\% c"), "a\\\\")

    def test_read_group(self):
        self.assertEqual(blueprint.read_group("{a{b}c}d", 0), ("a{b}c", 7))
        self.assertEqual(blueprint.read_group("[x {]} y]z", 0), ("x {]} y", 9))


class TestRepository(unittest.TestCase):
    """The parser on the nine blueprints of the repository."""

    def test_all_blueprints(self):
        files = sorted(glob.glob(str(ROOT / "*/blueprint/src/content.tex")))
        self.assertGreaterEqual(len(files), 9)
        total = 0
        for f in files:
            pkg = Path(f).parts[-4]
            tex = Path(f).read_text(encoding="utf-8")
            items = blueprint.parse(tex, pkg, f)
            labels = [i.label for i in items]
            self.assertEqual(len(labels), len(set(labels)), f"duplicate labels in {f}")
            self.assertFalse([i for i in items if i.label.startswith("line")],
                             f"items without a label in {f}")
            # every uncommented \lean{...} belongs to exactly one item
            n = len(re.findall(r"\\lean\{", blueprint.strip_comments(tex)))
            self.assertEqual(n, sum(1 for i in items), f)
            for i in items:
                self.assertTrue(i.lean, i.id)
                for name in i.lean:
                    self.assertRegex(name, r"^[\w.'!?]+$", i.id)
            total += len(items)
        self.assertGreater(total, 400)


if __name__ == "__main__":
    unittest.main()
