#!/usr/bin/env python3
"""Identity/order/duplicate regressions for the ordinary paired-fixture generator."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
from sourceOrdinaryPin import (BASE, CASES, PIN_ONLY_CASES, INHERITED_SOURCE_IDS,
                              align_imports, check_inherited_ids, check_inventory)


class ImportIdentityTest(unittest.TestCase):
    def setUp(self):
        self.modules = [dict(resolved_path=str(Path(p).resolve()),
                             source_sha256sum=h, source_id=i, body=[{'name': p}])
                        for p, h, i in [('main.vy', 'main-hash', 0),
                                        ('one.vyi', 'one-hash', 1),
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


class InheritedIdentityTest(unittest.TestCase):
    def test_duplicate_interface_uses_original_identity(self):
        name = 'duplicate_interface'
        entries = CASES[name]
        ids = INHERITED_SOURCE_IDS[name]
        self.assertEqual(ids[('utils', 'interfaces', 'IPing')], 1)
        legacy = json.loads((BASE/entries[0][1]).with_suffix('.json').read_text())
        check_inherited_ids(legacy, entries, ids)
        stale = {**ids, ('utils', 'interfaces', 'IPing'): 3}
        with self.assertRaises(AssertionError):
            check_inherited_ids(legacy, entries, stale)
        capture = json.loads((BASE/'source_ordinary'/f'{name}.json').read_text())
        interface = capture['inherited_origins'][1]
        self.assertEqual(interface['key'], ['utils', 'interfaces', 'IPing'])
        self.assertEqual((interface['source_id'], interface['module_id']), (1, 3))
        self.assertEqual(capture['annotated_ast']['imports'][0]['source_id'], 1)
        annotated = json.loads((BASE/'source_ordinary'/'annotated'/f'{name}.json').read_text())
        self.assertEqual(annotated['imports'][0]['source_id'], 1)

    def test_new_upstream_explicit_ids_match_legacy_evidence(self):
        for name, entries in PIN_ONLY_CASES.items():
            with self.subTest(name=name):
                legacy = json.loads((BASE/entries[0][1]).with_suffix('.json').read_text())
                check_inherited_ids(legacy, entries, INHERITED_SOURCE_IDS[name])


class FixtureInventoryTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        for entries in {**CASES, **PIN_ONLY_CASES}.values():
            source = self.base/entries[0][1]
            source.parent.mkdir(parents=True, exist_ok=True)
            source.touch()
            source.with_suffix('.json').touch()

    def test_exact_inventory_and_scope(self):
        check_inventory(self.base)
        check_inventory(BASE)
        self.assertEqual(len(CASES), 26)
        self.assertEqual(set(PIN_ONLY_CASES), {'attribute_initializes', 'nested_initializes',
            'imported_constants', 'interface_struct', 'relative_uses'})

    def test_new_unlisted_upstream_fixture_reject(self):
        (self.base/'new.vy').touch()
        (self.base/'new.json').touch()
        with self.assertRaisesRegex(AssertionError, "'unlisted': \\['new.vy'\\]"):
            check_inventory(self.base)

    def test_missing_retained_fixture_reject(self):
        (self.base/CASES['simple'][0][1]).with_suffix('.json').unlink()
        with self.assertRaisesRegex(AssertionError, "'missing': \\['simple.vy'\\]"):
            check_inventory(self.base)

    def test_source_captures_do_not_expand_upstream_inventory(self):
        source = self.base/'source_ordinary'/'pin_only'/'source.vy'
        source.parent.mkdir(parents=True)
        source.touch()
        source.with_suffix('.json').touch()
        check_inventory(self.base)


if __name__ == '__main__':
    unittest.main()
