"""Checks for the source-text metrics of tools/codebase_metrics.py."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from codebase_metrics import cone_sizes, measure


class TestMeasure(unittest.TestCase):
    """Metrics of a small project tree."""

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.write("a/aScript.sml", "Theory a\n\nDefinition f_def:\n  f = T\nEnd\n\n"
                   "Theorem f_thm[simp,local]:\n  f\nProof\n  cheat\nQED\n\n"
                   "Theorem g:\n  f /\\ T\nProof\n  rw[f_thm]\nQED\n\n"
                   "(* retired: (* inner *) Theorem z:\n  T\nProof\n  cheat\nQED\n*)\n")
        self.write("b/bScript.sml", "Theory b\nAncestors\n  a list\n\n(* Theorem c: T Proof cheat QED *)\n"
                   "Triviality h:\n  f   /\\\n  T\nProof\n  rw[g, g]\nQED\n")
        self.write("cScript.sml", "open HolKernel bTheory\nval _ = new_theory \"c\";\nDatatype:\n  t = C\nEnd\n"
                   "val k = store_thm(\"k[local]\", ``T``, rw[g]);\n")

    def write(self, path: str, text: str) -> None:
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text)

    def test_counts_skip_nested_comments(self) -> None:
        metrics = measure(self.root)
        self.assertEqual(metrics.dirs, {".": [1, 6], "a": [1, 24], "b": [1, 11]})
        self.assertEqual((metrics.theorems, metrics.trivialities, metrics.local_theorems), (3, 1, 2))
        self.assertEqual((metrics.definitions, metrics.datatypes, metrics.cheats), (1, 1, 1))

    def test_duplicate_statement_ignores_whitespace(self) -> None:
        self.assertEqual(measure(self.root).duplicate_statements, 1)

    def test_theorem_uses_count_declarations_not_mentions(self) -> None:
        metrics = measure(self.root)
        self.assertEqual((metrics.used_nowhere, metrics.used_once, metrics.used_more), (2, 1, 1))

    def test_cones_follow_headers_and_theory_references(self) -> None:
        metrics = measure(self.root)
        self.assertEqual(metrics.cone_largest, [("c", 2), ("b", 1), ("a", 0)])
        self.assertEqual(metrics.cone_median, 1)

    def test_cone_of_a_cycle(self) -> None:
        self.assertEqual(cone_sizes({"x": {"y"}, "y": {"x"}}), {"x": 1, "y": 1})


if __name__ == "__main__":
    unittest.main()
