"""Check scope boundaries and the two supported clump layouts."""

import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "clump.py"
spec = importlib.util.spec_from_file_location("clump", SCRIPT)
clump = importlib.util.module_from_spec(spec)
spec.loader.exec_module(clump)


class ClumpScopesTest(unittest.TestCase):
    def test_dotted_namespace_can_close_one_component_at_a_time(self):
        source = """@[expose] public section
namespace A.B
theorem inB : True := True.intro
end B
theorem inA : True := True.intro
end A"""
        scopes, declarations = clump.scan(source)
        self.assertEqual(scopes, [("section", None)])
        self.assertEqual(declarations, {"A.B.inB", "A.inA"})

    def test_named_scopes_can_share_one_end(self):
        for name in ("«B.C»", "«B C»", "«B--C»"):
            with self.subTest(name=name):
                source = f"section\nnamespace A.{name}-- a comment\nnamespace D"
                self.assertEqual(clump.closers(clump.open_scopes(source)),
                                 [f"end A.{name}.D" + clump.AUTO, "end" + clump.AUTO])
                scopes, names = clump.scan(source + f"\nend {name}.D\ntheorem t : True := .intro")
                self.assertEqual(scopes, [("section", None), ("namespace", "A")])
                self.assertEqual(names, {"A.t"})

    def test_existing_clump_after_a_preamble_is_protected(self):
        _, text = self.make_group()
        prefix = "set_option pp.universes true\n\n-- A local setting for these members.\n\n"
        text = text.replace(clump.CLUMP_MARK, prefix + clump.CLUMP_MARK)
        member = clump.Module("Example.C", "", text)
        self.assertTrue(clump.is_clump_file(member))

    def test_old_layout(self):
        header = "module\npublic import Init\n\n"
        info = json.dumps({"m": "Example.A", "h": header, "nonl": True})
        body = "theorem one : True := True.intro"
        text = "\n".join([clump.SEAM_BEGIN + "Example.A =====", clump.HEADER_TAG + info,
                          "section" + clump.AUTO, body, "end" + clump.AUTO,
                          clump.SEAM_END + "Example.A =====", ""])
        self.assertEqual(clump.unclump_text(text), {"Example.A": header + body})

    def make_group(self):
        common = "@[expose] public section\n\nopen Nat\nopen Bool\nopen List\n"
        sources = {
            "Example.A": "module\npublic import Init\n\n" + common + "\ntheorem one : True := True.intro\n\n",
            "Example.B": "module\npublic import Example.A\n\n" + common + "\ntheorem two : True := one",
            "Example.C": "module\npublic import Example.B\n\n@[expose] public section\n\ntheorem three : True := two\n",
        }
        mods = {name: clump.Module(name, "", source) for name, source in sources.items()}
        text = clump.render("", list(mods), mods)
        return sources, text

    def test_shared_namespace_opens_round_trip(self):
        sources, text = self.make_group()
        self.assertEqual(text.count("\nopen Nat\n"), 1)
        self.assertIn("\nsection " + clump.SHARED_OPENS, text)
        self.assertIn("\n" + clump.END_SHARED, text)
        self.assertGreater(text.index(clump.HEADER_TAG), text.index("theorem three"))
        self.assertEqual(clump.unclump_text(text), sources)
        edited = text.replace("\nopen Nat\n", "\nopen Int\n", 1)
        self.assertEqual(clump.unclump_text(edited),
                         {name: value.replace("\nopen Nat\n", "\nopen Int\n") for name, value in sources.items()})

    def write_project(self, root, sources):
        src = root / "src" / "Example"
        src.mkdir(parents=True)
        for name, text in sources.items():
            (src / (name.split(".")[-1] + ".lean")).write_text(text)
        subprocess.run(["git", "init", "-q", root], check=True)
        subprocess.run(["git", "-C", root, "add", "src"], check=True)
        return src

    def test_plan_keeps_existing_clumps_separate(self):
        sources, archive = self.make_group()
        members = list(sources)
        sources["Example.Archive"] = archive
        sources["Example.Tail"] = "module\npublic import Example.Archive\n\ntheorem tail : True := .intro\n"
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.write_project(root, sources)
            modules = clump.load_for_plan(root)
            self.assertEqual(clump.plan(modules, 1000), {"Example.C": members})
            self.assertEqual(clump.plan(modules, 1000, {"Example.B"}), {})

    def test_apply_reads_only_the_modules_in_the_plan(self):
        sources, _ = self.make_group()
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            src = self.write_project(root, sources)
            (src / "C.lean").unlink()

            with self.assertRaises(FileNotFoundError):
                clump.apply(root, {"Example.C": list(sources)})
            members = ["Example.A", "Example.B"]
            clump.apply(root, {"Example.B": members})
            self.assertFalse((src / "A.lean").exists())
            self.assertEqual(clump.unclump_text((src / "B.lean").read_text()),
                             {name: sources[name] for name in members})

    def test_temporary_open_stays_with_its_command(self):
        body = ["@[expose] public section", "open Int", "open Nat"]
        for tail in [["  Bool"], ["", "  Bool"], ["-- More namespaces", "  Bool"],
                     ["in", "#check zero"], ["(zero)"], ["hiding zero"]]:
            with self.subTest(tail=tail):
                self.assertEqual(clump.leading_opens(body + tail), ("open Int",))
        for open_line in ["open Nat in", "open Nat hiding zero", "open Nat (zero)"]:
            self.assertEqual(clump.leading_opens([body[0], open_line]), ())

    def test_separator_is_optional(self):
        sources, text = self.make_group()
        edited = text.replace("theorem two : True := one\nend" + clump.AUTO + "\n\n",
                              "theorem two : True := one\nend" + clump.AUTO + "\n")
        self.assertNotEqual(text, edited)
        self.assertEqual(clump.unclump_text(edited), sources)

    def test_remove_all_shared_opens(self):
        sources, text = self.make_group()
        block = "\nopen Nat\nopen Bool\nopen List\n"
        edited = text.replace(block, "\n", 1)
        self.assertEqual(clump.unclump_text(edited),
                         {name: value.replace(block, "\n") for name, value in sources.items()})

    def test_unassigned_text_is_reported(self):
        _, text = self.make_group()
        for edited in [text.replace("\nsection " + clump.SHARED_OPENS, "\nset_option pp.all true\nsection " + clump.SHARED_OPENS),
                       text.replace("open Nat", "theorem oneToo : True := True.intro", 1),
                       text + "set_option pp.all true\n",
                       text.replace(clump.END_SHARED, "", 1)]:
            with self.assertRaises(ValueError):
                clump.unclump_text(edited)

    def test_original_comment_can_use_the_new_marker(self):
        for marker in (clump.MEMBER_TAG + "note", clump.SHARED_OPENS, clump.HEADER_TAG + "note"):
            with self.subTest(marker=marker):
                source = f"module\n\n@[expose] public section\n{marker}\ntheorem one : True := True.intro\n"
                module = clump.Module("Example", "", source)
                text = clump.render("", ["Example"], {"Example": module})
                self.assertEqual(clump.unclump_text(text), {"Example": source})
                self.check_blame(text, [("theorem one", "Example")])

    def test_blame_marks_the_shared_group_and_each_member(self):
        _, text = self.make_group()
        self.check_blame(text, [("open Nat", "Example.A"), ("theorem two", "Example.B"), ("theorem three", "Example.C")])

    def test_markers_outside_the_archive_are_comments(self):
        preface = clump.MEMBER_TAG + "note\n" + clump.SEAM_BEGIN + "other =====\nexample : True := .intro\n"
        self.check_blame(preface, [("example", None)])
        sources, compact = self.make_group()
        self.assertEqual(clump.unclump_text(preface + compact), sources)
        self.check_blame(preface + compact, [("example", None), ("theorem two", "Example.B")])

    def check_blame(self, text, cases):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            source = root / "src" / "Example.lean"
            source.parent.mkdir()
            source.write_text(text)
            for snippet, name in cases:
                line = next(i for i, val in enumerate(text.splitlines(), 1) if val.startswith(snippet))
                log = root / "build.log"
                log.write_text(f"error: src/Example.lean:{line}:0: test error\n")
                self.assertEqual(clump.blame(root, [log]), [] if name is None else [name])


if __name__ == "__main__":
    unittest.main()
