import io
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import clump
import fold_serial


class SerialFoldTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.group = ["Lemmata.A", "Lemmata.R"]
        self.graph = {}
        self.a = "module\npublic import Core\n\ntheorem a : True := trivial"
        b = "module\npublic import Lemmata.A\n\ntheorem b : True := a\n"
        r = "module\npublic import Lemmata.B\n\ntheorem r : True := b\n"
        self.parts = {"Lemmata.A": self.a, "Lemmata.B": b, "Lemmata.R": r}
        members = {n: clump.Module(n, "", self.parts[n]) for n in ["Lemmata.B", "Lemmata.R"]}
        self.r = clump.render("Lemmata.R", list(members), members)
        # A batch added an import to the physical file after the first clump.
        self.r = self.r.replace("module\n", "module\npublic import New\n", 1)
        self.put("Lemmata.A", self.a)
        self.put("Lemmata.R", self.r)

    def put(self, name, text):
        path = self.root / "src" / Path(*name.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(text.encode())
        rows = [("Init", True, False), ("Init", True, True)]
        rows += [(n, p, False) for n, p in clump.Module(name, "", text).imports]
        self.graph[name] = [dict(module=n, isExported=p, isMeta=m, importAll=False)
                            for n, p, m in rows]

    def changes(self):
        return fold_serial.fold(self.root, [self.group], self.graph, set())

    def test_git_patch_restores_edited_members_and_keeps_current_header(self):
        edited = self.parts["Lemmata.B"].replace(":= a", ":= by exact a")
        self.put("Lemmata.R", self.r.replace(":= a\n", ":= by exact a\n"))
        self.parts["Lemmata.B"] = edited
        patch = io.StringIO()
        fold_serial.write_patch(self.changes(), patch)
        subprocess.run(["git", "apply"], input=patch.getvalue().encode(), cwd=self.root, check=True)
        self.assertFalse((self.root / "src/Lemmata/A.lean").exists())
        text = (self.root / "src/Lemmata/R.lean").read_text()
        self.assertEqual(clump.unclump_text(text), self.parts)
        self.assertEqual(clump.Module("Lemmata.R", "", text).imports, [("New", True), ("Core", True)])

    def test_helper_keeps_its_position_in_a_mixed_header(self):
        self.put("Lemmata.A", self.a.replace("public import Core", "public import Core\nimport Shared"))
        receiver = ("module\nimport First\npublic import Lemmata.A\npublic import Core\n"
                    "import Last\nimport Shared\n\ntheorem r : True := a\n")
        self.put("Lemmata.R", receiver)
        _, _, combined = self.changes()["Lemmata.R"]
        self.assertEqual(clump.Module("Lemmata.R", "", combined).imports,
                         [("First", False), ("Core", True), ("Last", False), ("Shared", False)])

    def test_deduplication_preserves_public_order(self):
        self.put("Lemmata.R", "module\nimport Core\npublic import First\npublic import Lemmata.A\n")
        with self.assertRaisesRegex(ValueError, "would reorder public imports"):
            self.changes()

    def test_all_obsolete_pairs_are_reported_before_writing_a_patch(self):
        groups = [("Lemmata.Missing1", "Lemmata.R"), ("Lemmata.A", "Lemmata.Missing2")]
        with self.assertRaises(ValueError) as failure:
            fold_serial.fold(self.root, groups, self.graph, set())
        self.assertIn("Lemmata.Missing1 -> Lemmata.R", str(failure.exception))
        self.assertIn("Lemmata.A -> Lemmata.Missing2", str(failure.exception))

    def test_external_importer_keeps_its_donor(self):
        self.put("Lemmata.Outside", self.parts["Lemmata.B"])
        with self.assertRaisesRegex(ValueError, "also imported by.*Lemmata.Outside"):
            self.changes()

    @unittest.skipUnless(shutil.which("lean"), "Lean parses the tracked import headers")
    def test_tracked_tool_outside_src_keeps_its_donor(self):
        tool = self.root / "tools/check.lean"
        tool.parent.mkdir()
        tool.write_text("import Lemmata.A\n")
        shutil.copyfile(Path(__file__).resolve().parents[2] / "lean-toolchain", self.root / "lean-toolchain")
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        subprocess.run(["git", "add", "src", "tools"], cwd=self.root, check=True)
        self.graph = fold_serial.project_imports(self.root)
        with self.assertRaisesRegex(ValueError, "also imported by.*tools/check.lean"):
            self.changes()

    def test_proof_outside_member_records_is_preserved(self):
        self.put("Lemmata.R", self.r + "\ntheorem addedByBatch : True := trivial\n")
        with self.assertRaisesRegex(ValueError, "do not reproduce the current body"):
            self.changes()

    def test_new_private_import_is_rejected(self):
        self.put("Lemmata.A", self.a.replace("public import Core", "import Core"))
        with self.assertRaisesRegex(ValueError, "would expose a new private import"):
            self.changes()


if __name__ == "__main__":
    unittest.main()
