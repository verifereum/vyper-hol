"""Checks which restated theorems dupscan reports."""

from __future__ import annotations

import contextlib
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import dupscan

BASE = """\
Definition foo_def:
  foo x y = x + y
End

Theorem foo_comm:
  !x y. foo x y = foo y x
Proof
  cheat
QED

Theorem foo_zero:
  foo x 0 = x
Proof
  cheat
QED
"""

NEW = """\
Definition bar_def:
  bar x y = x
End

Theorem foo_zero_bound:
  !n. foo n 0 = n
Proof
  cheat
QED

Theorem bar_zero:
  bar n 0 = n
Proof
  cheat
QED
"""


class TestScan(unittest.TestCase):
    """dupscan run on a repo whose last commit adds `bScript.sml`."""

    def scan(self, new: str) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)

            def commit(name: str, text: str) -> None:
                (repo / name).write_text(text)
                for args in (['add', name], ['commit', '-qm', name]):
                    subprocess.run(['git', '-c', 'user.name=t', '-c',
                                    'user.email=t@t', *args], cwd=repo,
                                   check=True)
            subprocess.run(['git', 'init', '-q'], cwd=repo, check=True)
            commit('aScript.sml', BASE)
            commit('bScript.sml', new)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                dupscan.main(tmp, 'HEAD~1', [])
        return out.getvalue().splitlines()[1:]

    def test_outer_binder_and_free_variable_names(self) -> None:
        self.assertEqual(self.scan(NEW), [
            "ALPHA bScript.sml foo_zero_bound -> [('aScript.sml', 'foo_zero')]"])

    def test_free_variables_renamed_consistently(self) -> None:
        self.assertEqual(self.scan(NEW.replace('foo n 0 = n', 'foo n 0 = x')), [])


class TestAlpha(unittest.TestCase):
    """Which names `alpha` renames."""

    def test_keeps_record_fields_and_antiquotations(self) -> None:
        self.assertEqual(
            dupscan.alpha('s.f = ^g (s with f := x)', {'s', 'f', 'g', 'x'}),
            'V0.f=^g(V0withf:=V1)')


def thm(name: str, stmt: str, proof: str = 'cheat') -> str:
    return f"Theorem {name}:\n  {stmt}\nProof\n  {proof}\nQED\n\n"


PRED = """\
Definition inv_def:
  inv x y <=> !z. p1 x /\\ p2 x /\\ p3 x /\\ p4 x /\\ p5 y /\\ p6 y /\\
                  p7 y /\\ p8 x y ==> q x y z
End
"""
EIGHT = 'p1 a /\\ p2 a /\\ p3 a /\\ p4 a /\\ p5 b /\\ p6 b /\\ p7 b /\\ p8 a b'
OPCODE = "Datatype:\n  opcode = ADD | SUB\nEnd\n"
PROOF = '\n  '.join(f'rw[step_{w}_lemma, other_{w}_fact] >> simp[]'
                    for w in ('one', 'two', 'three', 'four', 'five', 'six'))


class TestTree(unittest.TestCase):
    """What the whole-tree mode reports."""

    def hints(self, kind: str, **files: str) -> set[tuple[str, str]]:
        found = dupscan.scan_tree(files)
        return {(h[2], h[3]) for h in found.hints if h[0] == kind}

    def test_same_and_alpha_clusters(self) -> None:
        found = dupscan.scan_tree({
            'a': thm('t1', '!x. f x = x') + thm('t2', '!y. f y = y'),
            'b': thm('t3', '!x. f x = x') + thm('t4', '!x. g x = x')})
        self.assertEqual(sorted(sorted(c) for c in found.clusters['same']),
                         [[('a', 't1'), ('b', 't3')]])
        self.assertEqual(sorted(sorted(c) for c in found.clusters['alpha']),
                         [[('a', 't1'), ('a', 't2'), ('b', 't3')]])

    def test_short_re_exports_are_wrappers_not_copies(self) -> None:
        found = dupscan.scan_tree({
            'a': thm('t1', '!x. f x = x', PROOF),
            'b': thm('t1', '!y. f y = y', 'ACCEPT_TAC aTheory.t1'),
            'c': thm('t3', '!x. f x = x', 'metis_tac[t1]\n  >> simp[]'),
            'd': thm('t4', '!x. f x = x', PROOF + '\n  >> metis_tac[t1]')
                 + 'Theorem t5[simp] = aTheory.t1\n'})
        self.assertEqual(found.wrappers, {('b', 't1', 't1'), ('c', 't3', 't1'),
                                          ('d', 't5', 'aTheory.t1')})
        self.assertEqual([sorted(c) for c in found.clusters['same']],
                         [[('a', 't1'), ('d', 't4')]])
        self.assertEqual(found.clusters['alpha'], [])

    def test_wrapper_citation_must_name_the_members_theory(self) -> None:
        found = dupscan.scan_tree({
            'aScript.sml': thm('t1', '!x. f x = x', PROOF),
            'bScript.sml': thm('t1', '!x. f x = x', 'ACCEPT_TAC cTheory.t1'),
            'cScript.sml': 'Theorem t2 = REWRITE_RULE [] aTheory.t1\n'})
        self.assertEqual(found.wrappers, set())
        found = dupscan.scan_tree({
            'aScript.sml': thm('t1', '!x. f x = x', PROOF),
            'bScript.sml': thm('t1', '!x. f x = x', 'ACCEPT_TAC cTheory.t1'),
            'cScript.sml': 'Theorem t1 = aTheory.t1;\n'})
        self.assertEqual(found.wrappers, {('bScript.sml', 't1', 't1'),
                                          ('cScript.sml', 't1', 'aTheory.t1')})

    def test_wrapper_alias_must_re_export_the_member(self) -> None:
        found = dupscan.scan_tree({
            'aScript.sml': thm('t1', '!x. f x = x', PROOF),
            'bScript.sml': thm('t1', '!x. f x = x', 'ACCEPT_TAC cTheory.t1'),
            'cScript.sml': 'Theorem t1 = dTheory.other\n'})
        self.assertEqual(found.wrappers, {('cScript.sml', 't1', 'dTheory.other')})

    def test_wrapper_cites_through_an_alias_of_another_name(self) -> None:
        found = dupscan.scan_tree({
            'aScript.sml': thm('t1', '!x. f x = x', PROOF),
            'bScript.sml': thm('t2', '!x. f x = x', 'ACCEPT_TAC t1_alias'),
            'cScript.sml': 'Theorem t1_alias = aTheory.t1\n'})
        self.assertIn(('bScript.sml', 't2', 't1'), found.wrappers)

    def test_continued_right_hand_side_is_no_alias(self) -> None:
        found = dupscan.scan_tree({
            'a': 'Theorem t1 = make_thm\n  (some arg)\n\n'
                 'Theorem t2 = other_thm\n|> SPEC_ALL\n\n'
                 'Theorem t3 = third_thm\n\nTheorem t4 = last_thm'})
        self.assertEqual(found.wrappers, {('a', 't3', 'third_thm'), ('a', 't4', 'last_thm')})

    def test_wrapper_ignores_quoted_mentions(self) -> None:
        found = dupscan.scan_tree({
            'a': thm('t1', '!x. f x = x', PROOF),
            'b': thm('t2', '!x. f x = x', "qpat_x_assum `t1` mp_tac >> simp[]")})
        self.assertEqual(found.wrappers, set())

    def test_resumed_proof_is_part_of_the_proof(self) -> None:
        resume = '\nResume t2[rest]:\n  ' + PROOF + '\nQED\n'
        found = dupscan.scan_tree({
            'a': thm('t1', '!x. f x = x', PROOF),
            'b': thm('t2', '!x. f x = x', 'suspend "rest" >> metis_tac[t1]') + resume})
        self.assertEqual(found.wrappers, set())
        self.assertEqual([sorted(c) for c in found.clusters['proofs']],
                         [[('a', 't1'), ('b', 't2')]])

    def test_statement_on_the_theorem_line(self) -> None:
        found = dupscan.scan_tree({
            'a': 'Theorem t1[simp]: dimindex (:8) = 8\nProof\n  simp[]\nQED\n',
            'b': thm('t2', 'dimindex (:8) = 8')})
        self.assertEqual([sorted(c) for c in found.clusters['same']],
                         [[('a', 't1'), ('b', 't2')]])

    def test_commented_theorems_ignored(self) -> None:
        found = dupscan.scan_tree({
            'a': thm('t1', '!x. f x = x'),
            'b': '(* (* nested *)\n' + thm('t2', '!x. f x = x') + '*)\n'})
        self.assertEqual(found.clusters['same'], [])

    def test_near_identical_proofs_clustered(self) -> None:
        found = dupscan.scan_tree({
            'a': thm('t1', 'f = 1', PROOF) + thm('t2', 'g = 2', 'simp[]'),
            'b': thm('t1_mem', 'h = 3', PROOF.replace('simp[]', 'gvs[]', 1))})
        self.assertEqual([sorted(c) for c in found.clusters['proofs']],
                         [[('a', 't1'), ('b', 't1_mem')]])

    def test_restates_eight_conjuncts_of_a_predicate(self) -> None:
        self.assertEqual(self.hints('restates', a=PRED + thm(
            'restated', f'!a b. {EIGHT} ==> r a b')),
            {('restated', 'inv (8 conjuncts)')})

    def test_restates_equation_definition_and_bracketed_implication(self) -> None:
        pred = PRED.replace('<=> !z.', '= !z.')
        self.assertEqual(self.hints('restates', a=pred + thm(
            'restated', f'!a b. ({EIGHT} ==> r a b)')),
            {('restated', 'inv (8 conjuncts)')})

    def test_restates_equation_definition_with_equality_conjuncts(self) -> None:
        def eqs(v: str) -> str:
            return ' /\\ '.join(f'f{i} {v} = {i}' for i in range(8))
        pred = f'Definition inv_def:\n  inv x = !z. {eqs("x")} ==> q x z\nEnd\n'
        self.assertEqual(self.hints('restates', a=pred + thm(
            'restated', f'!a. {eqs("a")} ==> r a')), {('restated', 'inv (8 conjuncts)')})

    def test_restates_grouped_conjuncts(self) -> None:
        grouped = EIGHT.replace('p2 a /\\ p3 a', '(p2 a /\\ p3 a)')
        self.assertEqual(self.hints('restates', a=PRED + thm(
            'restated', f'!a b. {grouped} ==> r a b')),
            {('restated', 'inv (8 conjuncts)')})

    def test_restates_not_for_seven_conjuncts_or_using_the_predicate(self) -> None:
        seven = EIGHT.rsplit(' /\\ ', 1)[0]
        self.assertEqual(self.hints('restates', a=PRED + thm(
            'seven', f'!a b. {seven} ==> r a b') + thm(
            'intro', f'!a b. {EIGHT} ==> inv a b')), set())

    def test_variant_not_citing_its_base(self) -> None:
        self.assertEqual(self.hints('variant', a=thm('foo', 'f = 1')
                                    + thm('foo_own', 'f = 1 /\\ g = 2', 'simp[]')
                                    + thm('foo_live', 'f = 1', 'simp[foo]')
                                    + thm('foo_comm', 'f = 1', 'simp[]')
                                    + 'Theorem bar = cTheory.bar\n'
                                    + thm('bar_mem', 'g = 1', 'simp[]')
                                    + thm('baz', 'h = 1')
                                    + thm('baz_own', 'h = 1', "qpat_x_assum `baz` mp_tac")),
                         {('foo_own', 'foo'), ('bar_mem', 'bar'), ('baz_own', 'baz')})

    def test_instance_of_a_generic_lemma(self) -> None:
        self.assertEqual(self.hints('instance', a=OPCODE
                                    + thm('step_ok', '!op s. ok (step op s)')
                                    + thm('step_add_ok', '!s. ok (step ADD s)')
                                    + thm('step_sub_ok', '!s. ok (step SUB s)',
                                          'metis_tac[step_ok]')),
                         {('step_add_ok', 'a:step_ok at ADD')})

    def test_tree_mode_exits_zero_and_writes_tsvs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            (repo / 'aScript.sml').write_text(
                PRED + thm('t1', '!x. f x = x') + thm('t2', '!x. f x = x')
                + thm('restated', f'!a b. {EIGHT} ==> r a b'))
            subprocess.run(['git', 'init', '-q'], cwd=repo, check=True)
            subprocess.run(['git', 'add', '.'], cwd=repo, check=True)
            run = subprocess.run(
                [sys.executable, '-I', str(Path(dupscan.__file__)), '--tree',
                 str(repo / 'out'), tmp], capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            bad = subprocess.run(
                [sys.executable, '-I', str(Path(dupscan.__file__)), '--tree',
                 str(repo / 'out'), str(repo / 'missing')],
                capture_output=True, text=True)
            self.assertIn('is not a git checkout', bad.stderr)
            self.assertIn('same: 1 clusters, 2 theorems', run.stdout)
            self.assertEqual((repo / 'out' / 'same.tsv').read_text().splitlines(), [
                'cluster\tsize\tpath\tname',
                'aScript.sml:t1\t2\taScript.sml\tt1',
                'aScript.sml:t1\t2\taScript.sml\tt2'])
            self.assertIn('restates\taScript.sml\trestated\tinv (8 conjuncts)',
                          (repo / 'out' / 'hints.tsv').read_text())


if __name__ == '__main__':
    unittest.main()
