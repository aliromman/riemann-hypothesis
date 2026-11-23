from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import route_author_imports as routing
from partition_bundles import Partition, Source, git, read_graph, stage_sources


class AuthorImportTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name)
        subprocess.run(["git", "init", "--quiet", "--bare", str(self.repo)], check=True)
        header = "module\n\npublic import Mathlib\n"
        block = lambda name: "-- bundled from " + name + "\nsection\nexample : True := trivial\nend\n"
        self.original = {
            "Plain": Source(["Mathlib"]), "Uses": Source(["Mathlib", "Supplier"]),
            "Other": Source(["Mathlib"]), "Supplier": Source(["Mathlib"]),
        }
        self.input = {
            "Caller": header + "public import Items\npublic import Items\n" + block("Plain") + block("Uses"),
            "Items": header + block("Other") + block("Supplier"),
        }
        stage_sources(self.repo, self.input)
        self.routes = {"Caller": {"Items": [("Uses", "Supplier")]}}
        self.pinned = self.run_git("write-tree")
        with patch.object(routing, "AUTHOR_REVISION", self.pinned):
            routing.take_imports(self.repo, self.pinned, self.routes)
        self.stripped = self.run_git("write-tree")
        self.plan = Partition(self.original, read_graph(self.repo, self.stripped), ["Supplier"], [["Supplier"]])
        expanded = {}
        for target, previous in self.plan.previous.items():
            data = routing.source(self.repo, self.stripped, previous)
            expanded[target] = self.plan.render(target, data)
        stage_sources(self.repo, expanded)
        self.rendered = self.run_git("write-tree")

    def run_git(self, *args):
        return subprocess.check_output(git(self.repo, *args), text=True).strip()

    def test_repeated_import_follows_only_the_original_consumer(self):
        routed = routing.restore_imports(self.repo, self.rendered, self.routes, self.plan, ["Supplier"], [["Supplier"]])
        uses = self.plan.location["Uses"]
        supplier = self.plan.location["Supplier"]
        self.assertEqual(routed, {uses: [supplier]})
        final = read_graph(self.repo, self.run_git("write-tree"))
        self.assertEqual(final[uses].imports.count(supplier), 2)
        self.assertNotIn(supplier, final[self.plan.location["Plain"]].imports)

    def test_wrong_original_consumer_cannot_gain_the_protected_provider(self):
        bad = {"Caller": {"Items": [("Plain", "Supplier")]}}
        with self.assertRaisesRegex(ValueError, "change the protected choices"):
            routing.restore_imports(self.repo, self.rendered, bad, self.plan, ["Supplier"], [["Supplier"]])


if __name__ == "__main__":
    unittest.main()
