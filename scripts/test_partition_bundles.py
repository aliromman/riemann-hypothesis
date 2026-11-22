import unittest
from graphlib import CycleError
from pathlib import Path
from tempfile import TemporaryDirectory
import os
import shutil
import subprocess

from partition_bundles import ALL, META, PUBLIC, Partition, Source, changed_providers, read_graph


class PartitionTests(unittest.TestCase):
    def setUp(self):
        self.old = {
            "Provider": Source(["Mathlib"]),
            "Plain": Source(["Mathlib"]),
            "Uses": Source(["Wrapper"]),
            "Wrapper": Source(["Provider"]),
            "Caller": Source(["Plain"]),
            "User": Source(["Uses"]),
        }
        self.bundled = {
            "Provider": Source(["Mathlib"]),
            "Mixed": Source(["Mathlib", "Provider"], ["Plain", "Uses"]),
            "Caller": Source(["Mixed"]),
            "User": Source(["Mixed"]),
        }

    def test_split_after_wrapper_expansion(self):
        plan = Partition(self.old, self.bundled, ["Provider"])
        self.assertEqual(plan.differences, {"Plain": (0, 1), "Caller": (0, 1)})
        self.assertEqual(plan.location["Plain"], "Mixed")
        self.assertEqual(plan.location["Uses"], "Uses")
        self.assertEqual(plan.cone(["Caller"]), {"Caller", "Mixed"})
        self.assertEqual(plan.cone(["User"]), {"User", "Uses", "Provider"})
        preamble = "module\n\npublic import Mathlib\npublic import Provider\n\n"
        plain = "-- bundled from Plain\nsection\nexample : True := trivial\nend\n\n"
        uses = "-- bundled from Uses\nsection\nexample : True := trivial\nend\n"
        self.assertEqual(plan.render("Mixed", preamble + plain + uses), "module\n\npublic import Mathlib\n\n" + plain)
        self.assertEqual(plan.render("Uses", preamble + plain + uses), "module\n\npublic import Provider\n\n" + uses)

    def test_private_and_public_users_need_separate_bodies(self):
        old = {"P": Source(), "Private": Source(["P"], modes={"P": 0}), "Public": Source(["P"]),
               "Caller": Source(["Private"])}
        bundled = {"P": Source(), "Group": Source(["P"], ["Private", "Public"]), "Caller": Source(["Group"])}
        plan = Partition(old, bundled, ["P"])
        self.assertNotEqual(plan.location["Private"], plan.location["Public"])
        self.assertEqual(plan.render(plan.location["Private"], "public import P\n"), "import P\n")
        self.assertEqual(plan.render(plan.location["Public"], "public import P\n"), "public import P\n")

    def test_import_all_through_a_wrapper(self):
        old = {"P": Source(), "Wrapper": Source(["P"], modes={"P": ALL | META}),
               "Reader": Source(["Wrapper"], modes={"Wrapper": PUBLIC | ALL}), "Caller": Source(["Reader"])}
        submitted = {"P": Source(), "Reader": Source(["P"]), "Caller": Source(["Reader"])}
        plan = Partition(old, submitted, ["P"])
        self.assertTrue(plan.changed("Reader"))
        self.assertEqual(plan.render("Reader", "  public import P -- keep this\n"), "  meta import all P -- keep this\n")

    def test_rejects_inaccessible_transitive_dependency_of_removed_wrapper(self):
        self.old["Wrapper"].modes["Provider"] = 0
        with self.assertRaisesRegex(ValueError, "private edge Wrapper -> Provider"):
            Partition(self.old, self.bundled, ["Provider"])

    def test_public_and_all_imports_of_same_module(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src" / "P.lean").write_text("module\n")
            (root / "src" / "Reader.lean").write_text("module\npublic import P\nimport all P\n")
            subprocess.run(["git", "init", "--quiet", directory], check=True)
            subprocess.run(["git", "-C", directory, "add", "src"], check=True)
            tree = subprocess.check_output(["git", "-C", directory, "write-tree"], text=True).strip()
            self.assertEqual(read_graph(root, tree)["Reader"].modes["P"], PUBLIC | ALL)

    @unittest.skipUnless(shutil.which("lean"), "Lean is required for the instance-visibility fixture")
    def test_lean_observes_instance_only_through_public_import(self):
        key = "module\npublic import Lean\npublic class OriginalMarker (A : Type) where\n  tag : Nat\n"
        provider = "module\npublic import Key\npublic instance supplied : OriginalMarker Bool := ⟨19⟩\n"
        proof = "example : OriginalMarker Bool := inferInstance\n"

        def caller(dependency, expected):
            return (f"module\npublic import {dependency}\nopen Lean Elab Command\nrun_cmd\n"
                    "  let evidence ← liftTermElabM <| Meta.synthInstance? (mkApp (mkConst `OriginalMarker) (mkConst `Bool))\n"
                    f'  unless evidence.isSome == {expected} do throwError "incorrect provider visibility"\n')

        old = {"Key": Source(), "Provider": Source(["Key"]), "Priv": Source(["Key", "Provider"], modes={"Provider": 0}),
               "Pub": Source(["Key", "Provider"]), "FromPriv": Source(["Priv"]), "FromPub": Source(["Pub"])}
        bundled = {"Key": Source(), "Provider": Source(["Key"]), "Mixed": Source(["Key", "Provider"], ["Priv", "Pub"]),
                   "FromPriv": Source(["Mixed"]), "FromPub": Source(["Mixed"])}
        original = {"Key": key, "Provider": provider, "Priv": "module\npublic import Key\nimport Provider\n" + proof,
                    "Pub": "module\npublic import Key\npublic import Provider\n" + proof,
                    "FromPriv": caller("Priv", "false"), "FromPub": caller("Pub", "true")}
        body = "".join(f"-- bundled from {name}\nsection\n{proof}end\n" for name in ["Priv", "Pub"])
        submitted = {"Key": key, "Provider": provider, "Mixed": "module\npublic import Key\npublic import Provider\n" + body,
                     "FromPriv": caller("Mixed", "false"), "FromPub": caller("Mixed", "true")}
        plan = Partition(old, bundled, ["Provider"])
        corrected = {n: plan.render(n, submitted[plan.previous[n]]) for n in plan.members}

        with TemporaryDirectory() as directory:
            for label, sources, errors in [("original", original, set()), ("submitted", submitted, {"FromPriv"}),
                                           ("corrected", corrected, set())]:
                root = Path(directory) / label
                root.mkdir()
                env = dict(os.environ, LEAN_PATH=str(root))
                # The marker and provider must compile first, and the two consumers last.
                middle = [n for n in sources if n not in {"Key", "Provider", "FromPriv", "FromPub"}]
                failed = set()
                for name in ["Key", "Provider", *middle, "FromPriv", "FromPub"]:
                    source = root / (name + ".lean")
                    source.write_text(sources[name])
                    result = subprocess.run(["lean", "-R", str(root), "-o", str(root / (name + ".olean")), str(source)],
                                            env=env, capture_output=True, text=True)
                    if result.returncode:
                        self.assertIn("incorrect provider visibility", result.stdout + result.stderr)
                        failed.add(name)
                self.assertEqual(failed, errors, label)

    def test_provider_is_reachable_from_itself(self):
        plan = Partition({"P": Source(), "Q": Source()},
                         {"Both": Source([], ["P", "Q"])}, ["P", "Q"])
        self.assertEqual(len(plan.members), 2)
        self.assertEqual(plan.differences, {"P": (1, 3), "Q": (2, 3)})

    def test_report_emits_only_changed_provider_names_in_input_order(self):
        names = [f"Original{i}" for i in range(120)]
        self.assertEqual(list(changed_providers(0, names)), [])
        self.assertEqual(list(changed_providers((1 << 110) | 2, names)), ["Original1", "Original110"])

    def test_rejects_unexplained_import(self):
        self.bundled["Caller"].imports.append("Provider")
        with self.assertRaisesRegex(ValueError, "Wrapper expansion"):
            Partition(self.old, self.bundled, ["Provider"])

    def test_rejects_cyclic_input(self):
        self.old["Provider"].imports.append("User")
        with self.assertRaises(CycleError):
            Partition(self.old, self.bundled, ["Provider"])


if __name__ == "__main__":
    unittest.main()
