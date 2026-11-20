"""Checks for the used-set and statement index generator."""

from __future__ import annotations

import unittest

from proof_index import Graph, Saved, Theory, ancestor_sets, build_graph, listed, parse_dat, scan_script, statement_of

DAT = """(theory
 ("t" ("p" . "abc"))
 (core-data
  (tables (string-table "p" "t" "a" "b" "c"))
  exports (nil) (nil)
  ((2 (((1 0) (0 3)) "DISK_THM") (2 0) ("x"))
   (3 (((1 1) (1 0)) "DISK_THM") (2 0) ("x"))
   (4 (((1 2)) "DISK_THM") (1 0) ("x")))))
"""
EMPTY_DAT = """(theory ("r" ("t" . "abc") ("q" . "def"))
 (core-data (tables (string-table "r")) exports (nil) (nil) nil))
"""


class TestParseDat(unittest.TestCase):
    """Theorems, kinds and kernel dependencies read from theory data."""

    def test_records(self) -> None:
        thy = parse_dat(DAT, "tScript.sml")
        self.assertEqual((thy.name, thy.parents), ("t", ["p"]))
        self.assertEqual(thy.saved, [
            Saved("a", 0, "thm", [("p", [3])]),
            Saved("b", 1, "thm", [("t", [0])]),
            Saved("c", 2, "def", []),
        ])

    def test_empty_theory(self) -> None:
        thy = parse_dat(EMPTY_DAT, "rScript.sml")
        self.assertEqual((thy.parents, thy.saved), (["t", "q"], []))


SCRIPT = """Theory t
Ancestors p

Triviality helper:
  T
Proof
  simp[]
QED

Theorem split[local]:
  T /\\ T
Proof
  cheat
QED

Resume split[one]:
  simp[helper]
QED

Finalise split

(* TEMPORARILY CHEATED - slow
Proof
  metis_tac[kept_name]
QED
*)
Theorem cheated:
  !x. x ==> x
Proof
  cheat
QED

Theorem bound = helper

val _ = print_thm unused_by_proofs;
"""


class TestScanScript(unittest.TestCase):
    """Theorem blocks, their statements and proofs, read from a script."""

    def setUp(self) -> None:
        self.blocks, self.outside = scan_script(SCRIPT)

    def test_blocks(self) -> None:
        self.assertEqual(set(self.blocks), {"helper", "split", "cheated", "bound"})
        self.assertTrue(self.blocks["helper"][0].local)
        self.assertTrue(self.blocks["split"][0].local)
        self.assertFalse(self.blocks["cheated"][0].local)

    def test_statement_stops_at_proof(self) -> None:
        self.assertEqual(self.blocks["split"][0].statement, "T /\\ T")
        self.assertEqual(self.blocks["cheated"][0].statement, "!x. x ==> x")

    def test_resume_adds_to_the_proof(self) -> None:
        self.assertIn("helper", self.blocks["split"][0].proof)

    def test_kept_proof_above_resume(self) -> None:
        src = ("Theorem s:\n  T\nProof\n  cheat\nQED\n"
               "(* TEMPORARILY CHEATED - slow\nProof\n  simp[resumed_name]\nQED\n*)\n"
               "Resume s[a]:\n  cheat\nQED\n")
        blocks, _ = scan_script(src)
        self.assertIn("resumed_name", blocks["s"][0].kept)

    def test_simp_attribute(self) -> None:
        blocks, _ = scan_script("Theorem r[simp,local]:\n  T\nProof\n  simp[]\nQED\n")
        self.assertTrue(blocks["r"][0].simp and blocks["r"][0].local)

    def test_alias(self) -> None:
        blocks, _ = scan_script("Theorem a = pTheory.b\n\nTheorem c = REWRITE_RULE [] d\n")
        self.assertEqual(blocks["a"][0].alias, "pTheory.b")
        self.assertEqual(blocks["c"][0].alias, "")
        blocks, _ = scan_script("Theorem a = pTheory.b;\n")
        self.assertEqual(blocks["a"][0].alias, "pTheory.b")

    def test_save_thm(self) -> None:
        blocks, outside = scan_script('val p = save_thm("p",\n  prove(``T``, simp[]));\nval _ = save_thm ("q", q);\nval r = save_thm("r", other);\n')
        self.assertEqual((blocks["p"][0].statement, blocks["p"][0].line), ("T", 1))
        self.assertEqual(blocks["r"][0].alias, "other")
        self.assertNotIn("p", outside.split())
        self.assertNotIn("q", outside.replace(";", " ").split())

    def test_store_thm(self) -> None:
        blocks, _ = scan_script('val s = store_thm("s",\n  ``!x. x ==> x``,\n  simp[]);\n')
        self.assertEqual((blocks["s"][0].statement, blocks["s"][0].line), ("!x. x ==> x", 1))

    def test_finalise_local(self) -> None:
        blocks, _ = scan_script("Theorem s:\n  T\nProof\n  cheat\nQED\nResume s[a]:\n  simp[]\nQED\nFinalise s[local]\n")
        self.assertTrue(blocks["s"][0].local)

    def test_kept_proof_of_cheated_theorem(self) -> None:
        self.assertIn("kept_name", self.blocks["cheated"][0].kept)
        self.assertEqual(self.blocks["split"][0].kept, "")

    def test_kept_proof_is_not_in_the_statement(self) -> None:
        self.assertNotIn("kept_name", self.blocks["cheated"][0].statement)

    def test_code_outside_blocks(self) -> None:
        self.assertIn("unused_by_proofs", self.outside)
        self.assertNotIn("kept_name", self.outside)


class TestGraph(unittest.TestCase):
    """Uses through kernel dependencies, local names and kept proofs."""

    def graph(self) -> Graph:
        theories = {
            "p": Theory("p", "pScript.sml", [], [Saved("kept_name", 0, "thm", []), Saved("base", 3, "thm", [])]),
            "t": Theory("t", "tScript.sml", ["p"], [
                Saved("cheated", 0, "thm", []),
                Saved("split", 1, "thm", [("p", [3])]),
                Saved("bound", 2, "thm", []),
            ]),
        }
        return build_graph(theories, {"t": SCRIPT}, {})

    def test_kinds(self) -> None:
        nodes = self.graph().nodes
        self.assertEqual(nodes[("t", "helper")].kind, "local")
        self.assertEqual(nodes[("t", "split")].kind, "thm")  # saved despite [local]
        self.assertEqual(nodes[("p", "base")].kind, "gen")  # no script block

    def test_kernel_and_local_uses(self) -> None:
        reach = self.graph().closure([("t", "split")])
        self.assertEqual(reach, {("t", "split"), ("p", "base"), ("t", "helper")})

    def test_kept_proof_uses(self) -> None:
        reach = self.graph().closure([("t", "cheated")])
        self.assertIn(("p", "kept_name"), reach)

    def test_simp_local_used_by_later_theorems(self) -> None:
        src = ("Theorem early:\n  T\nProof\n  simp[]\nQED\n"
               "Theorem r[simp,local]:\n  T\nProof\n  simp[]\nQED\n"
               "Theorem late:\n  T\nProof\n  simp[]\nQED\n")
        theories = {"t": Theory("t", "tScript.sml", [], [Saved("early", 0, "thm", []), Saved("late", 1, "thm", [])])}
        g = build_graph(theories, {"t": src}, {})
        self.assertIn(("t", "r"), g.closure([("t", "late")]))
        self.assertNotIn(("t", "r"), g.closure([("t", "early")]))

    def test_alias_has_the_named_theorem_statement(self) -> None:
        theories = {
            "p": Theory("p", "pScript.sml", [], [Saved("b", 0, "thm", [])]),
            "t": Theory("t", "tScript.sml", ["p"], [Saved("b", 0, "thm", [])]),
        }
        g = build_graph(theories, {"p": "Theorem b:\n  x = y\nProof\n  cheat\nQED\n", "t": "Theorem b = pTheory.b\n"}, {})
        self.assertEqual(statement_of(g, ancestor_sets(theories), "t", "b"), "x = y")

    def test_code_outside_blocks_uses_exported_theorems(self) -> None:
        src = "Theorem e:\n  T\nProof\n  simp[]\nQED\n\nval _ = cv_trans (REWRITE_RULE [e] f_def);\n"
        theories = {"t": Theory("t", "tScript.sml", [], [Saved("e", 0, "thm", []), Saved("f_def", 1, "def", [])])}
        g = build_graph(theories, {"t": src}, {})
        self.assertIn(("t", "e"), g.closure([("t", "f_def")]))

    def test_local_reached_from_a_kept_proof_uses_what_its_proof_names(self) -> None:
        src = ("Theorem base:\n  T\nProof\n  simp[]\nQED\n"
               "Triviality helper:\n  T\nProof\n  simp[base, p_thm]\nQED\n"
               "(* TEMPORARILY CHEATED - slow\nProof\n  simp[helper]\nQED\n*)\n"
               "Theorem x:\n  T\nProof\n  cheat\nQED\n")
        theories = {
            "p": Theory("p", "pScript.sml", [], [Saved("p_thm", 0, "thm", [])]),
            "t": Theory("t", "tScript.sml", ["p"], [Saved("base", 0, "thm", []), Saved("x", 1, "thm", [])]),
        }
        g = build_graph(theories, {"t": src}, {})
        self.assertEqual(g.closure([("t", "x")]), {("t", "x"), ("t", "helper"), ("t", "base"), ("p", "p_thm")})

    def test_code_outside_blocks_uses_other_theories_theorems(self) -> None:
        src = "Theorem e:\n  T\nProof\n  simp[]\nQED\n\nval (a, b) = dest_forall (concl pTheory.p_thm);\n"
        theories = {
            "p": Theory("p", "pScript.sml", [], [Saved("p_thm", 0, "thm", [])]),
            "t": Theory("t", "tScript.sml", ["p"], [Saved("e", 0, "thm", [])]),
        }
        g = build_graph(theories, {"t": src}, {})
        self.assertIn(("p", "p_thm"), g.closure([("t", "e")]))

    def test_libraries_a_script_names_use_theorems(self) -> None:
        theories = {
            "p": Theory("p", "pScript.sml", [], [Saved("p_thm", 0, "thm", [])]),
            "t": Theory("t", "tScript.sml", ["p"], [Saved("e", 0, "thm", [])]),
        }
        g = build_graph(theories, {"t": "Theorem e:\n  T\nProof\n  simp[]\nQED\n"},
                        {"t": "fun tac g = REWRITE_TAC [pTheory.p_thm] g"})
        self.assertIn(("p", "p_thm"), g.closure([("t", "e")]))

    def test_code_outside_blocks_uses_locals(self) -> None:
        g = Graph({}, {}, {"t": {("t", "helper")}}, {})
        self.assertEqual(g.closure([("t", "x")]), {("t", "x"), ("t", "helper")})


class TestAncestors(unittest.TestCase):
    """Ancestor sets, through diamond imports."""

    def test_diamond(self) -> None:
        theories = {
            "root": Theory("root", "", ["b", "a"], []),
            "b": Theory("b", "", ["a"], []),
            "a": Theory("a", "", ["c"], []),
            "c": Theory("c", "", [], []),
        }
        anc = ancestor_sets(theories)
        self.assertEqual(anc["b"], {"a", "c"})
        self.assertEqual(anc["root"], {"a", "b", "c"})


class TestListed(unittest.TestCase):
    """Theories a rollup lists, through nested rollups."""

    def test_nested_rollups(self) -> None:
        theories = {
            "all": Theory("all", "", ["sub", "a"], []),
            "sub": Theory("sub", "", ["b"], []),
            "a": Theory("a", "", [], [Saved("x", 0, "thm", [])]),
            "b": Theory("b", "", ["c"], [Saved("y", 0, "thm", [])]),
            "c": Theory("c", "", [], [Saved("z", 0, "thm", [])]),
        }
        self.assertEqual(listed(theories, {}, "all"), {"a", "b"})

    def test_declared_ancestors_beyond_the_saved_fringe(self) -> None:
        theories = {
            "all": Theory("all", "", ["b"], []),  # a is imported by b, so not a saved parent
            "a": Theory("a", "", [], [Saved("x", 0, "thm", [])]),
            "b": Theory("b", "", ["a"], [Saved("y", 0, "thm", [])]),
        }
        self.assertEqual(listed(theories, {"all": ["a", "b"]}, "all"), {"a", "b"})


if __name__ == "__main__":
    unittest.main()
