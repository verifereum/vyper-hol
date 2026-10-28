#!/usr/bin/env python3
"""Identity/order/duplicate regressions for the ordinary paired-fixture generator."""
import copy
import unittest
from pathlib import Path
from sourceOrdinaryPin import align_imports


class ImportIdentityTest(unittest.TestCase):
    def setUp(self):
        self.modules = [dict(resolved_path=str(Path(p).resolve()),
                             source_sha256sum=h, source_id=i, body=[{'name': p}])
                        for p, h, i in [('main.vy', 'main-hash', 0),
                                        ('one.vyi', 'one-hash', 3),
                                        ('two.vy', 'two-hash', 2)]]
        self.identities = {(m['resolved_path'], m['source_sha256sum']):
                           {'source_id': m['source_id']} for m in self.modules}
        self.ast = {'ast': self.modules[0],
                    'imports': [self.modules[2], self.modules[1], copy.deepcopy(self.modules[1])]}

    def test_reorder_by_identity_and_equal_alias_dedupe(self):
        result = align_imports(self.ast, self.identities)
        self.assertEqual([result['ast']] + result['imports'], self.modules)

    def rejects(self, change):
        changed = copy.deepcopy(self.ast)
        change(changed)
        with self.assertRaises(AssertionError):
            align_imports(changed, self.identities)

    def test_same_source_different_declarations_reject(self):
        self.rejects(lambda a: a['imports'][2]['body'].append({'name': 'different'}))

    def test_different_hash_reject(self):
        self.rejects(lambda a: a['imports'][2].update(source_sha256sum='different'))

    def test_different_path_reject(self):
        self.rejects(lambda a: a['imports'][2].update(resolved_path='/different/one.vyi'))

    def test_different_source_id_reject(self):
        self.rejects(lambda a: a['imports'][2].update(source_id=99))

    def test_missing_import_reject(self):
        self.rejects(lambda a: a.update(imports=[self.modules[1]]))


if __name__ == '__main__':
    unittest.main()
