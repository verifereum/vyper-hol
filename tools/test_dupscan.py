"""Checks which restated theorems dupscan reports."""

from __future__ import annotations

import contextlib
import io
import subprocess
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


if __name__ == '__main__':
    unittest.main()
