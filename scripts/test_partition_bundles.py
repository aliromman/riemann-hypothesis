import unittest
from graphlib import CycleError

from partition_bundles import Partition, Source


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
        preamble = "module\n\npublic import Mathlib\npublic import all Provider\n\n"
        plain = "-- bundled from Plain\nsection\nexample : True := trivial\nend\n\n"
        uses = "-- bundled from Uses\nsection\nexample : True := trivial\nend\n"
        self.assertEqual(plan.render("Mixed", preamble + plain + uses), "module\n\npublic import Mathlib\n\n" + plain)
        self.assertEqual(plan.render("Uses", preamble + plain + uses), "module\n\npublic import all Provider\n\n" + uses)

    def test_provider_is_reachable_from_itself(self):
        plan = Partition({"P": Source(), "Q": Source()},
                         {"Both": Source([], ["P", "Q"])}, ["P", "Q"])
        self.assertEqual(len(plan.members), 2)
        self.assertEqual(plan.differences, {"P": (1, 3), "Q": (2, 3)})

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
