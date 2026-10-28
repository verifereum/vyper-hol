"""Checks for the build targets of CI jobs that build part of the project."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from ci_targets import Header, Project, Witnesses, WitnessTimes, median_build_times, test_dependencies


class ProjectTestCase(unittest.TestCase):
    """A temporary project tree; `write` adds files to it."""

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)

    def write(self, path: str, text: str = "") -> Path:
        """Write `text` to `path` under the project root."""
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text)
        return file


class TestHeader(ProjectTestCase):
    """Ancestors and Libs read from a theory script header."""

    def test_sections_span_indented_lines(self) -> None:
        script = self.write("aScript.sml", "Theory a[no_sig_docs]\nAncestors\n  b c\n  d\nLibs e\n    f\n\nDefinition x = T\nEnd\n")
        self.assertEqual(Header.read(script), Header("a", ("b", "c", "d"), ("e", "f")))

    def test_comments_and_attributes_are_skipped(self) -> None:
        script = self.write("aScript.sml", "(* Theory z *)\nTheory a\nAncestors b[qualified] (* c *) d\n")
        self.assertEqual(Header.read(script), Header("a", ("b", "d"), ()))

    def test_body_ends_the_header(self) -> None:
        script = self.write("aScript.sml", "Theory a\nAncestors b\nopen c\nLibs d\n")
        self.assertEqual(Header.read(script).libs, ())

    def test_script_without_theory_line_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "has no 'Theory <name>' line"):
            Header.read(self.write("aScript.sml", "open HolKernel\n"))


class TestTestDependencies(ProjectTestCase):
    """What the test groups load besides the generated test theories."""

    def test_generated_theories_and_hol_names_are_left_out(self) -> None:
        self.write("tests/generated/vyperTestDefs_aScript.sml", "Theory vyperTestDefs_a\nAncestors jsonToVyper list\nLibs vyperTestLib\n")
        self.write("tests/generated/vyperTest_aScript.sml", "Theory vyperTest_a\nAncestors vyperTestDefs_a\nLibs vyperTestRunnerLib computeLib\n")
        self.write("tests/vyperTestCoverageReportScript.sml", "Theory vyperTestCoverageReport\nLibs vyperTestLib\n")
        self.write("tests/jsonToVyperScript.sml", "Theory jsonToVyper\n")
        self.write("tests/vyperTestLib.sml")
        self.write("tests/vyperTestRunnerLib.sml")
        self.assertEqual(test_dependencies(Project(self.root)),
                         ["jsonToVyperTheory", "vyperTestLib", "vyperTestRunnerLib"])


def witness(name: str, ancestors: str = "compileVyper", fixtures: int = 1) -> str:
    """A witness script evaluating `fixtures` fixture programs."""
    calls = "".join(f'val f{k} = memoryStoreWitnessLib.evaluate root "f{k}"\n' for k in range(fixtures))
    return f"Theory {name}\nAncestors {ancestors}\nLibs memoryStoreWitnessLib computeLib\n\n{calls}"


class WitnessProjectTestCase(ProjectTestCase):
    """A project whose witness rollup reaches witnesses a, b (on c) and c, plus a rollup r."""

    def setUp(self) -> None:
        super().setUp()
        self.write("holproject.toml", '[build]\nroots = ["mainScript.sml", "lowering/evalCompilerWitnessesScript.sml"]\n'
                                      '[dependencies.dep]\nrev = "0"\n')
        self.write(".holbuild/src/dep/holproject.toml", '[build]\nroots = ["depScript.sml"]\n')
        self.write(".holbuild/src/dep/depScript.sml", "Theory dep\n")
        self.write("mainScript.sml", "Theory main\nAncestors compileVyper\n")
        self.write("lowering/evalCompilerWitnessesScript.sml", "Theory evalCompilerWitnesses\nAncestors a r\n")
        self.write("compileVyperScript.sml", "Theory compileVyper\n")
        self.write("memoryStoreWitnessLib.sml")
        self.write("aScript.sml", witness("a", fixtures=4))
        self.write("rScript.sml", "Theory r\nAncestors b\n")
        self.write("bScript.sml", witness("b", "compileVyper c", fixtures=2))
        self.write("cScript.sml", witness("c"))
        self.witnesses = Witnesses(Project(self.root))


class TestWitnesses(WitnessProjectTestCase):
    """The witnesses, what they need, and what the build job builds instead."""

    def test_witnesses_are_the_witness_lib_users_only_the_rollup_reaches(self) -> None:
        self.assertEqual(self.witnesses.names, ["a", "b", "c"])

    def test_build_roots_leave_out_the_rollup_and_add_dependency_roots(self) -> None:
        self.assertEqual(self.witnesses.build_roots(), ["mainTheory", "depTheory"])

    def test_unfetched_dependency_is_rejected(self) -> None:
        (self.root / ".holbuild/src/dep/holproject.toml").unlink()
        with self.assertRaisesRegex(ValueError, "run `holbuild buildhol` first"):
            self.witnesses.build_roots()

    def test_compiler_is_what_witnesses_load_besides_witnesses(self) -> None:
        self.assertEqual(self.witnesses.compiler(), ["compileVyperTheory", "memoryStoreWitnessLib"])

    def test_witnesses_on_other_witnesses_form_one_unit(self) -> None:
        self.assertEqual(self.witnesses.units(), [["a"], ["b", "c"]])

    def test_fixtures_count_evaluate_calls(self) -> None:
        self.assertEqual([self.witnesses.fixtures(n) for n in self.witnesses.names], [4, 2, 1])


class TestWitnessTimes(WitnessProjectTestCase):
    """Witness time estimates and the groups planned from them."""

    def test_times_scale_with_fixtures_and_new_witnesses_take_the_median_rate(self) -> None:
        times = WitnessTimes({"a": (200.0, 2), "b": (100.0, 2), "gone": (50.0, 1)}, self.witnesses)
        self.assertEqual(times.seconds, {"a": 400.0, "b": 100.0, "c": 50.0})

    def test_a_witness_waits_for_its_witness_ancestors(self) -> None:
        times = WitnessTimes({"a": (40.0, 4), "b": (20.0, 2), "c": (30.0, 1)}, self.witnesses)
        self.assertEqual(times.makespan(["c", "b", "a"]), 50.0)

    def test_units_stay_together_and_every_witness_is_planned_once(self) -> None:
        times = WitnessTimes({"a": (40.0, 4), "b": (20.0, 2), "c": (30.0, 1)}, self.witnesses)
        self.assertEqual(times.plan(self.witnesses.units(), 2), [["c", "b"], ["a"]])

    def test_empty_times_file_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "names no witnesses"):
            WitnessTimes({}, self.witnesses)


class TestMedianBuildTimes(unittest.TestCase):
    """Witness times read from CI `built in` log lines."""

    def test_median_of_the_named_theories_only(self) -> None:
        logs = ["2026-10-26T00:00:00.0Z aTheory built in 10s\n2026-10-26T00:00:00.0Z zTheory built in 1s",
                "2026-10-26T00:00:00.0Z aTheory built in 30.5s"]
        self.assertEqual(median_build_times(logs, ["a"]), {"a": 20.25})


if __name__ == "__main__":
    unittest.main()
