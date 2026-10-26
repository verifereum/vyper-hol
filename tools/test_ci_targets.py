"""Checks for the build targets of CI jobs that build part of the project."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from ci_targets import Header, Project, test_dependencies


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


if __name__ == "__main__":
    unittest.main()
