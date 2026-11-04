import json
import tempfile
import unittest
from pathlib import Path

from statement_checker import checks


def make(item="p:thm:a", reviewer="Ada Lovelace", date="2026-11-01T10:00:00Z",
         verdict="agrees", comment="", lh="0" * 16, sh="1" * 16):
    return checks.Check(item=item, reviewer=reviewer, date=date, verdict=verdict,
                        comment=comment, lean_hash=lh, source_hash=sh, lean=("P.a",))


class TestHashing(unittest.TestCase):
    def test_digest(self):
        self.assertEqual(checks.digest("abc"), checks.digest("abc"))
        self.assertNotEqual(checks.digest("abc"), checks.digest("abd"))
        self.assertRegex(checks.digest("x"), r"^[0-9a-f]{16}$")
        # stable across runs and machines (sha256 prefix)
        self.assertEqual(checks.digest(""), "e3b0c44298fc1c14")

    def test_slug(self):
        self.assertEqual(checks.slug("Niccolò D'Archivio"), "niccolo-d-archivio")
        self.assertEqual(checks.slug("  "), "reviewer")


class TestRecords(unittest.TestCase):
    def test_validate_record(self):
        good = json.loads(make().to_json())
        self.assertEqual(checks.validate_record(good), [])
        bad = dict(good, verdict="maybe")
        self.assertTrue(checks.validate_record(bad))
        self.assertTrue(checks.validate_record(dict(good, verdict="differs", comment=" ")))
        self.assertEqual(checks.validate_record(dict(good, verdict="differs", comment="c")), [])
        self.assertTrue(checks.validate_record(dict(good, verdict="unsure")))
        self.assertTrue(checks.validate_record(dict(good, date="yesterday")))
        self.assertTrue(checks.validate_record(dict(good, lean_hash="xyz")))
        self.assertTrue(checks.validate_record({k: v for k, v in good.items() if k != "item"}))
        self.assertTrue(checks.validate_record([1, 2]))

    def test_store_roundtrip_and_problems(self):
        with tempfile.TemporaryDirectory() as d:
            st = checks.Store(d)
            self.assertEqual(st.checks, [])
            st.append(make())
            st.append(make(reviewer="Alan Turing", verdict="differs", comment="constants"))
            files = sorted(p.name for p in Path(d).glob("*.jsonl"))
            self.assertEqual(files, ["ada-lovelace.jsonl", "alan-turing.jsonl"])
            with self.assertRaises(ValueError):
                st.append(make(verdict="unsure"))
            # a file without a final newline, a broken line and a bad record
            p = Path(d) / "ada-lovelace.jsonl"
            p.write_text(p.read_text().rstrip("\n"))
            st.append(make(date="2026-11-02T10:00:00Z"))
            with open(Path(d) / "broken.jsonl", "w") as f:
                f.write("{not json\n")
                f.write(json.dumps({"item": "x"}) + "\n")
            st2 = checks.Store(d)
            self.assertEqual(len(st2.checks), 3)
            self.assertEqual(len(st2.problems), 1 + 6)  # bad JSON; 6 missing fields
            self.assertTrue(all(line.strip() for line in p.read_text().split("\n")[:-1]))

    def test_union_merge(self):
        """Two branches append different lines to the same file; git's union merge keeps
        both sides. The result must load as the union of the checks."""
        a = make(item="p:thm:a").to_json()
        b = make(item="p:thm:b").to_json()
        base = make(item="p:thm:0").to_json()
        with tempfile.TemporaryDirectory() as d:
            Path(d, "ada-lovelace.jsonl").write_text("\n".join([base, a, b]) + "\n")
            st = checks.Store(d)
            self.assertEqual(sorted(c.item for c in st.checks), ["p:thm:0", "p:thm:a", "p:thm:b"])


class TestStatus(unittest.TestCase):
    def test_latest_and_stale(self):
        lh, sh = "a" * 16, "b" * 16
        cs = [make(verdict="unsure", comment="q", lh=lh, sh=sh, date="2026-11-01T10:00:00Z"),
              make(verdict="agrees", lh=lh, sh=sh, date="2026-11-02T10:00:00Z"),
              make(reviewer="Alan Turing", verdict="differs", comment="c", lh="c" * 16, sh=sh),
              make(reviewer="Grace Hopper", verdict="agrees", lh=lh, sh="d" * 16)]
        st = checks.status(cs, lh, sh, me="Ada Lovelace")
        self.assertEqual(st.agrees, ("Ada Lovelace",))
        self.assertEqual(st.n, 1)
        self.assertEqual(st.stale, ("Alan Turing", "Grace Hopper"))
        self.assertEqual(st.differs, ())
        self.assertEqual(st.mine.verdict, "agrees")
        self.assertFalse(st.mine_stale)
        self.assertEqual(checks.stale_parts(cs[2], lh, sh), ["Lean"])
        self.assertEqual(checks.stale_parts(cs[3], lh, sh), ["source"])
        # a later `unsure` replaces an earlier `agrees` of the same reviewer
        cs.append(make(verdict="unsure", comment="why?", lh=lh, sh=sh, date="2026-11-03T10:00:00Z"))
        st = checks.status(cs, lh, sh, me="Ada Lovelace")
        self.assertEqual(st.n, 0)
        self.assertEqual(st.unsure, ("Ada Lovelace",))
        # when the text changes, all checks become stale
        st = checks.status(cs, "e" * 16, sh)
        self.assertEqual(st.n, 0)
        self.assertEqual(len(st.stale), 3)


if __name__ == "__main__":
    unittest.main()
