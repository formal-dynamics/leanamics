import glob
import unittest
from pathlib import Path

from statement_checker import blueprint, lean_decls
from statement_checker.model import Model
from statement_checker.tests import ROOT

SAMPLE = '''import Mathlib

/-! # Module doc with `theorem fake : True := trivial` inside -/

namespace Foo
open Finset

variable {V C : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 2 ≤ n)

/-- A configuration. -/
abbrev Config (V C : Type*) := V → C

/-- One step. -/
noncomputable def step (s : Config V C) (r : V → V) : Config V C :=
  fun i => s (r i)  -- a comment with := inside

omit [DecidableEq V] in
/-- A lemma
spanning two lines. -/
@[simp] theorem step_const (c : C) (r : V → V) :
    step (fun _ : V => c) r = fun _ => c := by
  rfl

theorem uses_n (h : 3 ≤ n) : (n : ℝ) ≥ 3 ∧ "a := b" = "a := b" := by
  sorry

include hn in
lemma with_hyp : 1 ≤ n := by omega

private lemma helper : True := trivial

theorem by_cases : ∀ k : ℕ, k = k
  | 0 => rfl
  | k + 1 => rfl

section Inner
variable (G : SimpleGraph V)

/-- A structure. -/
structure Good (x : ℕ) : Prop where
  pos : 0 < x
  /-- documented field -/
  small big : x < 10

inductive Colour
  | red
  | blue (k : ℕ)

instance instFoo : Inhabited (Config V Bool) := ⟨fun _ => true⟩

theorem _root_.Bar.baz (h : G.Connected) : True := trivial

end Inner

namespace Deep.Er
def q : ℕ := 1
end Deep.Er

end Foo

theorem top_level : True := trivial
'''


class TestSample(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        decls = lean_decls.parse_file(SAMPLE, "pkg", "pkg/Foo.lean")
        cls.idx = lean_decls.Index(decls)
        cls.d = cls.idx.by_name

    def test_names(self):
        for n in ["Foo.Config", "Foo.step", "Foo.step_const", "Foo.uses_n", "Foo.with_hyp",
                  "Foo.helper", "Foo.by_cases", "Foo.Good", "Foo.Good.pos", "Foo.Good.small",
                  "Foo.Good.big", "Foo.Good.mk", "Foo.Colour.red", "Foo.Colour.blue",
                  "Foo.instFoo", "Bar.baz", "Foo.Deep.Er.q", "top_level"]:
            self.assertIn(n, self.d, n)
        self.assertNotIn("fake", self.d)
        self.assertNotIn("Foo.fake", self.d)
        self.assertTrue(self.d["Foo.helper"].private)

    def test_kinds_and_lines(self):
        self.assertEqual(self.d["Foo.Config"].kind, "abbrev")
        self.assertEqual(self.d["Foo.step_const"].kind, "theorem")
        self.assertEqual(self.d["Foo.step_const"].line, 20)
        self.assertEqual(self.d["Foo.Good.pos"].kind, "field")
        self.assertEqual(self.d["Foo.Colour.blue"].kind, "constructor")
        self.assertTrue(self.d["Foo.Good"].is_definition)
        self.assertFalse(self.d["Foo.uses_n"].is_definition)

    def test_docstrings(self):
        self.assertEqual(self.d["Foo.step"].doc, "One step.")
        self.assertEqual(self.d["Foo.step_const"].doc, "A lemma\nspanning two lines.")
        self.assertEqual(self.d["Foo.uses_n"].doc, "")

    def test_statement_cut(self):
        sc = self.d["Foo.step_const"].statement
        self.assertTrue(sc.startswith("@[simp] theorem step_const"))
        self.assertTrue(sc.endswith("fun _ => c"))
        self.assertNotIn("rfl", sc)
        # := inside a string does not cut the statement
        self.assertIn('"a := b" = "a := b"', self.d["Foo.uses_n"].statement)
        self.assertNotIn("sorry", self.d["Foo.uses_n"].statement)
        # pattern matching
        self.assertEqual(self.d["Foo.by_cases"].statement.strip(),
                         "theorem by_cases : ∀ k : ℕ, k = k")
        # definitions keep their body (and their comments)
        self.assertIn("fun i => s (r i)", self.d["Foo.step"].statement)
        self.assertNotIn("Inner", self.d["Foo.instFoo"].text)

    def test_variables(self):
        self.assertEqual(self.d["Foo.step"].variables,
                         ["{V C : Type*}", "[Fintype V]", "[DecidableEq V]"])
        # omit removes the binder
        self.assertEqual(self.d["Foo.step_const"].variables, ["{V C : Type*}", "[Fintype V]"])
        # a hypothesis variable is used only when mentioned or included
        self.assertEqual(self.d["Foo.uses_n"].variables, ["(n : ℕ)"])
        self.assertEqual(self.d["Foo.with_hyp"].variables, ["(n : ℕ)", "(hn : 2 ≤ n)"])
        # the declaration's own binders shadow section variables
        self.assertEqual(self.d["Foo.Config"].variables, [])
        self.assertIn("(G : SimpleGraph V)", self.d["Bar.baz"].variables)

    def test_refs(self):
        refs = self.idx.refs(self.d["Foo.step_const"])
        self.assertEqual(refs, ["Foo.step"])
        self.assertEqual(self.idx.refs(self.d["Foo.step"]), ["Foo.Config"])

    def test_hash_ignores_proofs_and_comments(self):
        a = self.d["Foo.step_const"].check_text()
        other = SAMPLE.replace("  rfl\n\ntheorem uses_n", "  simp [step]\n\ntheorem uses_n")
        other = other.replace("/-- A lemma\nspanning", "/-- Another lemma\nspanning")
        d2 = lean_decls.Index(lean_decls.parse_file(other, "pkg", "x")).by_name
        self.assertEqual(a, d2["Foo.step_const"].check_text())
        changed = SAMPLE.replace("step (fun _ : V => c) r = fun _ => c",
                                 "step (fun _ : V => c) r = fun _ => c ∧ True")
        d3 = lean_decls.Index(lean_decls.parse_file(changed, "pkg", "x")).by_name
        self.assertNotEqual(a, d3["Foo.step_const"].check_text())


class TestLibrary(unittest.TestCase):
    """The extractor on the whole library: every \\lean{} name of the blueprints is found."""

    @classmethod
    def setUpClass(cls):
        cls.model = Model(ROOT, checks_dir=Path("/nonexistent-checks-dir"))

    def test_every_blueprint_name_resolves(self):
        missing = [(e.id, n) for e in self.model.entries for n in e.missing]
        self.assertEqual(missing, [], f"names not found: {missing}")

    def test_library_names_are_found_in_library(self):
        """All names but the few Mathlib ones resolve to the library's own sources."""
        ext = sorted({n for e in self.model.entries for n, d in e.decls
                      if d is not None and d.package == "mathlib"})
        self.assertLessEqual(len(ext), 5, ext)

    def test_theorem_statements_have_no_proofs(self):
        for e in self.model.entries:
            for n, d in e.decls:
                if d is None or d.is_definition or d.package == "mathlib":
                    continue
                code = lean_decls.mask(d.statement)
                self.assertNotIn(":= by", code, n)
                self.assertNotIn("\n  rw ", code, n)

    def test_no_duplicate_public_names(self):
        dup = [n for n, ds in self.model.index.duplicates.items()
               if sum(1 for d in ds if not d.private) > 1]
        self.assertEqual(dup, [])

    def test_counts_are_plausible(self):
        files = lean_decls.lean_files(ROOT)
        self.assertGreater(len(files), 300)
        self.assertGreater(len(self.model.index.by_name), 3000)
        defs = sum(1 for e in self.model.entries for n, d in e.decls if d and d.is_definition)
        self.assertGreater(defs, 300)


if __name__ == "__main__":
    unittest.main()
