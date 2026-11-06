import contextlib
import io
import tempfile
import textwrap
import unittest
from pathlib import Path

from statement_checker import cli, latex, render, sources
from statement_checker.model import Model
from statement_checker.tests import ROOT

LEAN = '''\
namespace Toy

variable {n : ℕ}

/-- The toy predicate. -/
def Good (x : ℕ) : Prop := 2 ≤ x

/-- **Theorem 1.** Every large number is good. -/
theorem good_of_large (x : ℕ) (h : 3 ≤ x) : Good x := by
  unfold Good
  omega

end Toy
'''

TEX = r'''
\begin{abstract}A toy package. It has one theorem.\end{abstract}
\section{Toy}
\begin{definition}[Good numbers]\label{def:good}\lean{Toy.Good}\leanok
A number is good if it is at least $2$.
\end{definition}
\begin{theorem}[Theorem 1]\label{thm:one}\lean{Toy.good_of_large}\leanok\uses{def:good}
Every $x \ge 3$ is good.
\end{theorem}
'''

SOURCES = """
[[source]]
item = "toy:thm:one"
paper = "A. Author. Toy numbers"
version = "arXiv:0000.00000v1"
result = "Theorem 1"
status = "transcribed from the arXiv LaTeX source, not yet compared with the PDF"
statement = '''
Every integer $x \\geq 3$ is good.
'''
"""


class ToyRepo:
    """A minimal repository with one package `toy`."""

    def __init__(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "toy" / "Toy").mkdir(parents=True)
        (self.root / "toy" / "lakefile.toml").write_text('name = "toy"\n')
        (self.root / "toy" / "Toy" / "Basic.lean").write_text(LEAN)
        bp = self.root / "toy" / "blueprint" / "src"
        bp.mkdir(parents=True)
        (bp / "content.tex").write_text(TEX)
        (self.root / "verification").mkdir()
        (self.root / "verification" / "sources.toml").write_text(SOURCES)

    def model(self, reviewer="Ada Lovelace"):
        return Model(self.root, reviewer=reviewer)

    def edit(self, rel, old, new):
        p = self.root / rel
        text = p.read_text()
        assert old in text, old
        p.write_text(text.replace(old, new))


class TestToyRepository(unittest.TestCase):
    def setUp(self):
        self.repo = ToyRepo()

    def tearDown(self):
        self.repo.tmp.cleanup()

    def test_items_and_sources(self):
        m = self.repo.model()
        self.assertEqual([e.id for e in m.entries], ["toy:def:good", "toy:thm:one"])
        thm = m.by_id["toy:thm:one"]
        self.assertEqual(thm.used, ["Toy.Good"])
        self.assertEqual(len(thm.sources), 1)
        self.assertEqual(thm.tier, 0)
        self.assertEqual(m.by_id["toy:def:good"].tier, 1)  # used by a main result
        self.assertEqual(cli.validate(m), [])

    def test_staleness(self):
        m = self.repo.model()
        m.record(m.by_id["toy:thm:one"], "agrees", "")
        m.record(m.by_id["toy:def:good"], "agrees", "")
        self.assertEqual(m.status(m.by_id["toy:thm:one"]).n, 1)
        # a new proof, a new doc comment and a new comment do not change the statement
        self.repo.edit("toy/Toy/Basic.lean", "  unfold Good\n  omega", "  simp [Good]; omega")
        self.repo.edit("toy/Toy/Basic.lean", "Every large number", "Large numbers")
        m = self.repo.model()
        self.assertEqual(m.status(m.by_id["toy:thm:one"]).n, 1)
        self.assertEqual(m.status(m.by_id["toy:thm:one"]).stale, ())
        # a changed hypothesis does
        self.repo.edit("toy/Toy/Basic.lean", "(h : 3 ≤ x)", "(h : 2 ≤ x)")
        m = self.repo.model()
        st = m.status(m.by_id["toy:thm:one"])
        self.assertEqual((st.n, st.stale), (0, ("Ada Lovelace",)))
        self.assertTrue(st.mine_stale)
        # so does a changed definition body, for the definition's own item
        self.repo.edit("toy/Toy/Basic.lean", ":= 2 ≤ x", ":= 1 ≤ x")
        m = self.repo.model()
        self.assertEqual(m.status(m.by_id["toy:def:good"]).stale, ("Ada Lovelace",))
        # and a changed source transcription
        m.record(m.by_id["toy:thm:one"], "agrees", "")
        self.repo.edit("verification/sources.toml", "geq 3", "geq 4")
        m = self.repo.model()
        c = m.status(m.by_id["toy:thm:one"])
        self.assertEqual(c.stale, ("Ada Lovelace",))
        # a changed blueprint statement too
        m.record(m.by_id["toy:thm:one"], "agrees", "")
        self.repo.edit("toy/blueprint/src/content.tex", "Every $x \\ge 3$", "Every $x \\ge 4$")
        m = self.repo.model()
        self.assertEqual(m.status(m.by_id["toy:thm:one"]).stale, ("Ada Lovelace",))

    def test_record_rules(self):
        m = self.repo.model()
        e = m.by_id["toy:thm:one"]
        with self.assertRaises(ValueError):
            m.record(e, "differs", "  ")
        with self.assertRaises(ValueError):
            m.record(e, "wrong", "x")
        with self.assertRaises(ValueError):
            self.repo.model(reviewer=None).record(e, "agrees", "")
        m.record(e, "differs", "the paper has 2 instead of 3; intended")
        m2 = self.repo.model(reviewer="Alan Turing")
        st = m2.status(m2.by_id["toy:thm:one"])
        self.assertEqual(st.differs, ("Ada Lovelace",))
        self.assertIsNone(st.mine)

    def test_validate_reports_errors(self):
        (self.repo.root / "verification" / "checks").mkdir()
        (self.repo.root / "verification" / "checks" / "ada-lovelace.jsonl").write_text(
            '{"item": "toy:thm:nope", "reviewer": "Ada Lovelace", "date": "2026-11-01T10:00:00Z",'
            ' "verdict": "agrees", "comment": "", "lean_hash": "0000000000000000",'
            ' "source_hash": "0000000000000000"}\n{broken\n')
        self.repo.edit("toy/blueprint/src/content.tex", r"\lean{Toy.Good}",
                       r"\lean{Toy.Good,Toy.Missing}")
        self.repo.edit("verification/sources.toml", 'item = "toy:thm:one"', 'item = "toy:thm:two"')
        probs = cli.validate(self.repo.model())
        text = "\n".join(probs)
        self.assertIn("unknown item `toy:thm:nope`", text)
        self.assertIn("invalid JSON", text)
        self.assertIn("Toy.Missing", text)
        self.assertIn("unknown item `toy:thm:two`", text)

    def run_cli(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = cli.main(["--root", str(self.repo.root), "--reviewer", "Ada Lovelace", *args])
        return code, out.getvalue(), err.getvalue()

    def test_next_and_record(self):
        code, out, _ = self.run_cli("--next")
        self.assertEqual((code, out.strip()), (0, "toy:thm:one"))
        code, out, _ = self.run_cli("--next", "--skip", "toy:thm:one")
        self.assertEqual((code, out.strip()), (0, "toy:def:good"))
        code, _, err = self.run_cli("--record", "toy:thm:one", "--verdict", "agrees")
        self.assertEqual(code, 2)
        self.assertIn("--basis", err)
        code, _, err = self.run_cli("--record", "toy:thm:one", "--verdict", "differs",
                                    "--basis", "paper")
        self.assertEqual(code, 2)
        self.assertIn("nothing recorded", err)
        code, out, _ = self.run_cli("--record", "toy:thm:one", "--verdict", "agrees",
                                    "--basis", "transcription")
        self.assertEqual(code, 0)
        self.assertIn("ada-lovelace.jsonl", out)
        m = self.repo.model()
        self.assertEqual(m.store.checks[0].basis, "transcription")
        self.assertEqual(cli.validate(m), [])
        self.assertIn("| transcription | 1 |", cli.report(m))
        code, out, _ = self.run_cli("--next")
        self.assertEqual(out.strip(), "toy:def:good")
        self.run_cli("--record", "toy:def:good", "--verdict", "unsure", "--basis", "blueprint",
                     "--comment", "is 2 right?")
        code, out, _ = self.run_cli("--next")   # unsure is not a check
        self.assertEqual(out.strip(), "toy:def:good")
        code, out, _ = self.run_cli("--next", "--skip", "toy:def:good")
        self.assertEqual(code, 1)

    def test_package_sources_dir(self):
        d = self.repo.root / "verification" / "sources"
        d.mkdir()
        (d / "toy.toml").write_text(SOURCES.replace("toy:thm:one", "toy:def:good")
                                    .replace("Theorem 1", "Definition 1"))
        m = self.repo.model()
        self.assertEqual(len(m.source_entries), 2)
        self.assertEqual(m.by_id["toy:def:good"].sources[0]["result"], "Definition 1")
        self.assertEqual(cli.validate(m), [])

    def test_report_and_render(self):
        m = self.repo.model()
        m.record(m.by_id["toy:thm:one"], "agrees", "")
        m.record(m.by_id["toy:def:good"], "unsure", "is 2 right?")
        rep = cli.report(m)
        self.assertIn("| `toy` | 2 | 1 | 1 | 0 | 0 | 0 | 1 |", rep)
        self.assertIn("is 2 right?", rep)
        lines = [t for t, _ in render.detail(m, m.by_id["toy:thm:one"], 80)]
        text = "\n".join(lines)
        for part in ("Every integer x ≥ 3 is good.", "theorem good_of_large", "Toy.Good",
                     "→ toy:def:good", "agrees: Ada Lovelace"):
            self.assertIn(part, text)
        self.assertTrue(all(render.cwidth(t) <= 80 for t in lines))
        ctx = render.item_context(m, m.by_id["toy:thm:one"], "Why 3?")
        self.assertIn("Why 3?", ctx)
        self.assertIn("def Good (x : ℕ) : Prop := 2 ≤ x", ctx)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = cli.main(["--root", str(self.repo.root), "--list", "--reviewer", "X"])
        self.assertEqual(code, 0)
        self.assertIn("toy:thm:one", out.getvalue())


class TestRepository(unittest.TestCase):
    """The real repository: everything validates, and the report is complete."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.m = Model(ROOT, checks_dir=Path(cls.tmp.name) / "checks", reviewer="Test")

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_validate(self):
        self.assertEqual(cli.validate(self.m), [])

    def test_sources_file(self):
        self.assertEqual(self.m.source_problems, [])
        self.assertGreater(len(self.m.source_entries), 20)
        for s in self.m.source_entries:
            # Every entry says how its text was obtained; an entry without a statement
            # (no open copy of the source) must say so.
            self.assertTrue(s["status"].strip(), s["items"])
            if not s.get("statement"):
                self.assertNotIn("compared with the PDF", s["status"], s["items"])
            self.assertNotIn("checked by", s["status"].replace("not checked by", "")
                             .replace("not yet checked by", ""), s["items"])
            for i in s["items"]:
                self.assertIn(i, self.m.by_id)

    def test_every_item_renders(self):
        for e in self.m.entries:
            lines = render.detail(self.m, e, 80)
            self.assertTrue(all(render.cwidth(t) <= 80 for t, _ in lines), e.id)

    def test_priority(self):
        tiers = [e.tier for e in self.m.priority]
        self.assertEqual(tiers, sorted(tiers))
        self.assertEqual(self.m.by_id["plurality:thm:3_8"].tier, 0)
        self.assertLessEqual(self.m.by_id["plurality:def:config"].tier, 1)

    def test_provenance_matching(self):
        e = self.m.by_id["voter:thm:21"]
        self.assertTrue(any("Hassin" in r.text() for r in e.provenance))


class TestLatexAndSources(unittest.TestCase):
    def test_render(self):
        r = latex.render
        self.assertEqual(r(r"$\alpha \le \beta$"), "α ≤ β")
        self.assertEqual(r(r"$x^2 + y_{i} \ge \frac{1}{2}$"), "x² + yᵢ ≥ 1/2")
        self.assertEqual(r(r"$\sqrt{n \log n}$"), "√(n log n)")
        self.assertEqual(r(r"$\mathbb{E}[X] \in \mathbb{R}$"), "𝔼[X] ∈ ℝ")
        self.assertEqual(r(r"Erd\H{o}s--R\'enyi"), "Erdős–Rényi")
        self.assertEqual(r(r"\texttt{foo\_bar} and \emph{x}"), "foo_bar and x")
        self.assertEqual(r(r"$\lceil 3 \log n\rceil$"), "⌈3 log n⌉")
        self.assertEqual(r(r"see Lemma~\ref{lem:a}"), "see Lemma [lem:a]")
        self.assertEqual(r(r"$\unknownmacro{x}{\alpha}$"), r"\unknownmacro{x}{α}")
        self.assertEqual(r("a\n\nb\nc"), "a\n\nb c")
        self.assertEqual(r(r"$n^{1/4-\delta}$"), "n¹ᐟ⁴⁻ᵟ")
        self.assertEqual(r(r"$n^{1/y}$"), "n^{1/y}")

    def test_links(self):
        self.assertEqual(sources.links("see arXiv:1310.2858 (v1) and doi:10.1145/2612669.2612677."),
                         ["https://arxiv.org/abs/1310.2858",
                          "https://doi.org/10.1145/2612669.2612677"])
        self.assertEqual(sources.links("https://arxiv.org/abs/1702.04921v1"),
                         ["https://arxiv.org/abs/1702.04921v1"])

    def test_tables(self):
        self.assertEqual(sources.split_row(r"| a | `x \| y` | c |"), ["a", "`x | y`", "c"])
        self.assertEqual(sources.expand_token("lemma_3_1_a/b/c"),
                         ["lemma_3_1_a", "lemma_3_1_b", "lemma_3_1_c"])
        cands = sources._namespaced_candidates(["Voter.potential_drift_mul", "lazy_x"])
        self.assertIn("Voter.lazy_x", cands)


if __name__ == "__main__":
    unittest.main()
