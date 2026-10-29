#!/usr/bin/env python3
"""Pin acceptance and genuine pre-erasure captures of the ordinary fixture universe.

Run with the pinned checkout on PYTHONPATH; --generate refreshes both sides.
CASES is the retained HOL gate; PIN_ONLY_CASES audits newer upstream fixtures
without claiming source elaboration, kernel checking, or backend coverage.
The inherited ID table is explicit trust, not inferred by pairing similar ASTs.
Compiler and pre-erasure capture receive the SAME pinned source and source ID.
Stale version pragmas are reported separately and adapted copies retain ALL
other declarations. No compiler inferred expression type enters source trust.
"""
import argparse
import hashlib
import json
import runpy
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'tests/fixtures/check_contract'
OUT = BASE / 'source_ordinary'
CASES = {
    **{n: [(('main',), n + '.vy')] for n in ['simple', 'storage', 'address_bytes20',
       'constant_bound', 'constant_shifts', 'constant_shift_overflow', 'calldata_slice',
       'in_static_array', 'nested_pop', 'decimal_folding', 'raw_call_calldata', 'unreachable']},
    **{n: [(('main',), n + '/main.vy')] + [(('lib',), n + '/lib.vy')] for n in
       ['scoped_locals', 'imported_flag', 'imported_struct', 'imported_deploy', 'multimodule_storage']},
    **{n: [(('main',), n + '/main.vy')] for n in ['defaults_control', 'deployment',
       'nonreentrant', 'transient_storage', 'abi_encode']},
    'imported_interface': [(('main',), 'imported_interface/main.vy'), (('oracle',), 'imported_interface/oracle.vyi')],
    'interface_struct_return': [(('main',), 'interface_struct_return/main.vy'), (('manager',), 'interface_struct_return/manager.vyi')],
    'duplicate_interface': [(('main','c'), 'duplicate_interface/main/c.vy'),
        (('utils','interfaces','IPing'), 'duplicate_interface/utils/interfaces/IPing.vyi'),
        (('utils','pinger'), 'duplicate_interface/utils/pinger.vy')],
    'daddy': [(('main',), 'third_party/flex/daddy/daddy.vy')],
}


# New upstream checker fixtures are pin/capture audits only, not additions to
# sourceOrdinaryFixtureLib.rows or the 26-case ordinary HOL inventory.
PIN_ONLY_CASES = {
    **{n: [(('main',), n + '/main.vy'), (('ownable',), n + '/ownable.vy'),
            (('token',), n + '/token.vy')]
       for n in ['attribute_initializes', 'nested_initializes']},
    'imported_constants': [(('main',), 'imported_constants/main.vy'),
        (('lib1',), 'imported_constants/lib1.vy'), (('lib2',), 'imported_constants/lib2.vy')],
    'interface_struct': [(('main',), 'interface_struct/main.vy'), (('I',), 'interface_struct/I.vyi')],
    'relative_uses': [(('pkg', 'mocks', 'main'), 'relative_uses/pkg/mocks/main.vy'),
        (('pkg', 'lib_a'), 'relative_uses/pkg/lib_a.vy'),
        (('pkg', 'lib_b'), 'relative_uses/pkg/lib_b.vy')],
}


# Inherited legacy module IDs are source IDs + 2 (main is NONE). These
# declarations are independent of compiler traversal order and body syntax.
INHERITED_SOURCE_IDS = {
    **{n: {('main',): 0, ('lib',): 1} for n in
       ['scoped_locals', 'imported_flag', 'imported_struct', 'imported_deploy', 'multimodule_storage']},
    'imported_interface': {('main',): 0, ('oracle',): 1},
    'interface_struct_return': {('main',): 0, ('manager',): 1},
    'duplicate_interface': {('main', 'c'): 0, ('utils', 'interfaces', 'IPing'): 1,
                            ('utils', 'pinger'): 2},
    **{n: {('main',): 0, ('ownable',): 2, ('token',): 1}
       for n in ['attribute_initializes', 'nested_initializes']},
    'imported_constants': {('main',): 0, ('lib1',): 2, ('lib2',): 1},
    'interface_struct': {('main',): 0, ('I',): 1},
    'relative_uses': {('pkg', 'mocks', 'main'): 0, ('pkg', 'lib_a'): 1, ('pkg', 'lib_b'): 2},
}


def check_inventory(base):
    ordinary = {str(p.with_suffix('.vy').relative_to(base)) for p in base.rglob('*.json')
        if p.with_suffix('.vy').exists() and not any(part.startswith('source_') for part in p.relative_to(base).parts)}
    assert not CASES.keys() & PIN_ONLY_CASES.keys(), 'overlapping HOL/pin-only inventories'
    expected = {entries[0][1] for entries in {**CASES, **PIN_ONLY_CASES}.values()}
    assert ordinary == expected, ('ordinary fixture inventory drift',
        {'unlisted': sorted(ordinary - expected), 'missing': sorted(expected - ordinary)})
    assert len(CASES) == 26
    assert len(PIN_ONLY_CASES) == 5


def check_inherited_ids(annotated, entries, ids):
    """Check explicit IDs against independent retained legacy fixture evidence.

    Do not infer a trust map from compiler output or pair similar module bodies.
    Equal aliases may repeat a path; conflicting IDs or extra imports fail.
    """
    expected = {path: ids[key] for key, path in entries}
    found = {}
    for module in [annotated['ast']] + annotated['imports']:
        path, source_id = module['resolved_path'], module['source_id']
        assert path in expected, ('unexpected legacy import', path)
        assert source_id == expected[path], ('legacy source ID disagrees with explicit trust', path)
        found[path] = source_id
    assert found == expected, 'missing legacy import'


def align_imports(annotated, identities):
    """Retain manifest order by actual path + hash, never by syntax/array zip.

    Vyper emits duplicate interface aliases. Dedupe only identical full module
    claims at the same path/hash/ID (therefore identical declarations too).
    A divergent duplicate is an error, not an import silently discarded.
    """
    found = {}
    for module in [annotated['ast']] + annotated['imports']:
        identity = (str(Path(module['resolved_path']).resolve()), module['source_sha256sum'])
        assert identity in identities, ('unexpected compiler import', identity)
        assert module['source_id'] == identities[identity]['source_id']
        if identity in found:
            assert module == found[identity], ('divergent duplicate import', identity)
        else:
            found[identity] = module
    assert found.keys() == identities.keys(), 'missing compiler import'
    ordered = [found[identity] for identity in identities]
    return {**annotated, 'ast': ordered[0], 'imports': ordered[1:]}


def main(generate):
    import vyper
    from vyper.compiler.input_bundle import FilesystemInputBundle
    from vyper.compiler.settings import Settings
    pin = (ROOT / 'VYPER_PIN').read_text().strip()
    checkout = ROOT / '.agent-files/folded-value-validation/vyper-src'
    assert subprocess.check_output(['git','-C',checkout,'rev-parse','HEAD'], text=True).strip() == pin
    assert not subprocess.check_output(['git','-C',checkout,'status','--porcelain'], text=True), 'dirty authoritative pin checkout'
    for path in Path(vyper.__file__).resolve().parent.rglob('*.py'):
        relative = path.relative_to(Path(vyper.__file__).resolve().parent)
        assert str(relative) == 'version.py' or path.read_bytes() == (checkout/'vyper'/relative).read_bytes(), relative
    check_inventory(BASE)
    capture = runpy.run_path(str(ROOT / 'tools/source_module_loader.py'))['capture']
    OUT.mkdir(exist_ok=True)
    rows = []
    for name, entries in {**CASES, **PIN_ONLY_CASES}.items():
        pin_only = name in PIN_ONLY_CASES
        output = OUT/'pin_only' if pin_only else OUT
        row = {'name':name, 'scope':'pin-only' if pin_only else 'retained-HOL-gate',
               'sources':[p for _,p in entries]}
        ids = INHERITED_SOURCE_IDS.get(name, {entries[0][0]: 0})
        # These upstream fixtures retain path/ID metadata. Some older,
        # hand-authored ordinary oracles do not carry that provenance.
        if pin_only or name == 'duplicate_interface':
            legacy = json.loads((BASE/entries[0][1]).with_suffix('.json').read_text())
            check_inherited_ids(legacy.get('annotated_ast', legacy), entries, ids)
        paths = [BASE/p for _,p in entries]
        row['original_sha256'] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        search = [paths[0].parent, BASE/'duplicate_interface']
        def manifest_for(ps):
            return [{'key': list(key), 'path': str(p.resolve()), 'source_id': ids[key]}
                    for (key, _), p in zip(entries, ps)]
        def compile_paths(ps):
            manifest = manifest_for(ps)
            origins = {Path(e['path']): e['source_id'] for e in manifest}
            bundle = FilesystemInputBundle(search + [ps[0].parent])
            # The pinned FilesystemInputBundle allocates through its base
            # class, so seed its explicit path registry before loading ANY
            # file. Unknown/new imports fail the identity inventory below.
            bundle._source_ids = origins.copy()
            bundle._source_id_counter = max(origins.values()) + 1
            file_input = bundle.load_file(ps[0].resolve())
            return vyper.compile_from_file_input(file_input, input_bundle=bundle,
                settings=Settings(enable_decimals=True), output_formats=['annotated_ast_dict'])['annotated_ast_dict']
        try:
            compile_paths(paths)
            row['original_pin'] = 'ACCEPT'
        except Exception as error:
            row['original_pin'] = type(error).__name__
            row['original_diagnostic'] = str(error)
        stale = any('#pragma version 0.5.0a3' in p.read_text() for p in paths)
        if stale:
            adapted = []
            for p in paths:
                dest = OUT/'adapted'/p.relative_to(BASE)
                text = p.read_text().replace('#pragma version 0.5.0a3', '#pragma version 0.5.0a4')
                if generate:
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.write_text(text)
                else:
                    assert dest.read_text() == text
                adapted.append(dest)
            paths = adapted
            row['adaptation'] = 'version pragma only; not original-source acceptance'
            try:
                compile_paths(paths)
                row['adapted_pin'] = 'ACCEPT'
            except Exception as error:
                row['adapted_pin'] = type(error).__name__
                row['adapted_diagnostic'] = str(error)
        row['sha256'] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        try:
            manifest = manifest_for(paths)
            captured = capture(manifest)
            identities = {(e['path'], p['source_sha256']): e
                          for e, p in zip(manifest, captured['provenance'])}
            annotated = align_imports(compile_paths(paths), identities)
            # Persist the independently selected inherited origin map, with
            # actual file identity. No module body or expression is supplied.
            captured['inherited_origins'] = [
                {**e, 'source_sha256': p['source_sha256'],
                 'module_id': None if i == 0 else e['source_id'] + 2}
                for i, (e, p) in enumerate(zip(manifest, captured['provenance']))]
            for dest, value in [(output/(name+'.json'), captured),
                                (output/'annotated'/(name+'.json'), annotated)]:
                text = json.dumps(value,sort_keys=True,separators=(',',':')) + '\n'
                if generate:
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.write_text(text)
                else:
                    assert dest.read_text() == text, dest
            row['inherited_origins'] = captured['inherited_origins']
            row['capture'] = 'PASS'
        except Exception as error:
            row['capture'] = type(error).__name__
            row['capture_diagnostic'] = str(error)
        rows.append(row)
        print(name, row['original_pin'], row.get('adapted_pin',''), row['capture'], flush=True)
    (ROOT/'.agent-files/source-ordinary-pin.json').write_text(json.dumps({'pin':pin,'settings':{'enable_decimals':True},'rows':rows},indent=2)+'\n')
    assert all(r['capture'] == 'PASS' for r in rows), 'pre-erasure capture failure'
    assert all(r['original_pin'] == 'ACCEPT' if 'adaptation' not in r else
        r['original_pin'] == 'VersionException' and r['adapted_pin'] == 'ACCEPT' for r in rows), 'pin acceptance failure'

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate', action='store_true')
    main(parser.parse_args().generate)
