"""Summarize observed matrix output without treating dependency residuals as MATCH."""
import hashlib
import json
from collections import Counter
from pathlib import Path
from memory_store_witnesses import first_difference

root = Path(__file__).resolve().parent / 'memory-construction-matrix'
preparation = json.loads((root / 'preparation.json').read_text())
prerequisites = {
    'arr_dyn_lit_string': '#551 dynamic bytestring-array ABI encoding',
    'arr_string_local_lit': '#551 dynamic bytestring-array ABI encoding',
    'arr_string_ret_lit': '#551 dynamic bytestring-array ABI encoding',
    'list_of_bytes': '#551 dynamic bytestring-array ABI encoding',
    'p05_int_local_dynarray': '#545 internal local DynArray lowering',
    'x03_assign_elem_from_pop': '#550 RHS-before-target evaluation',
    'g2_a_dyn_nested': '#559 nested array append/pop lowering',
    'p11_pop_local_struct_field': '#559 field/nested array append/pop lowering',
    'p12_pop_local_nested': '#559 field/nested array append/pop lowering',
    'p18_append_local_struct_field': '#559 field/nested array append/pop lowering',
    'p19_pop_local_struct_word': '#559 field/nested array append/pop lowering',
    'in_empty_list': '#569 membership lowering',
    'c04_const_array': '#565 constant aggregate lowering',
    'c17_const_dynarray': '#565 constant aggregate lowering',
    'i03_immut_dynarray': '#563 immutable aggregate lowering',
    'm05_imm_dynarray_index_in_ctor': '#563 immutable aggregate lowering; HOL evaluation residual, not a byte comparison',
    'm06_imm_dynarray_index_runtime': '#563 immutable aggregate lowering',
    'p30_imm_dynarray': '#563 immutable aggregate lowering',
    'm38_const_in_type': 'TASK does not supply imported libp module source; Python cannot resolve libp',
}
observed = dict(line.split('\t', 1) for line in (root / 'results.tsv').read_text().splitlines())
rows = {}
for name, prepared in preparation['witnesses'].items():
    row = dict(prepared)
    row['observed'] = observed.get(name, 'NOT_RUN: Python rejected input')
    if name in prerequisites:
        row['prerequisite'] = prerequisites[name]
    if row['observed'] == 'PARITY_DEFECT' and name not in prerequisites:
        raise ValueError(('unclassified mismatch', name))
    if row['observed'] in ('MATCH', 'PARITY_DEFECT'):
        def read_bytes(path):
            return {key: bytes.fromhex(value) for key, value in
                (line.split('=', 1) for line in path.read_text().splitlines())}
        real = read_bytes(root / 'oracle' / (name + '.hex'))
        hol = read_bytes(root / 'hol' / (name + '.hex'))
        row['sections'] = {section: {'python_bytes': len(real[section]),
            'hol_bytes': len(hol[section]),
            'first_difference': first_difference(real[section], hol[section])}
            for section in ('deploy', 'runtime')}
    rows[name] = row
report = {'provenance': {key: value for key, value in preparation.items() if key != 'witnesses'},
    'counts': dict(Counter(row['observed'] for row in rows.values())),
    'witnesses': rows,
    'artifact_sha256': {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
        for sub in ('sources', 'oracle') for path in sorted((root / sub).glob('*'))
        if path.suffix in ('.vy', '.json', '.hex')},
    'extra_checked_fixture': 'arr_dyn_lit_word is covered by evalCompilerMemoryConstructionTheory (not repeated in matrix)',
    'source_unavailable': ['f02', 'g15: names referenced in TASK but complete source not supplied'],
    'behavior': 'Eight differential EVM cases reproduced by executeMemoryConstructionTheory; c10(7)=0, c11(7)=7'}
(root / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report['counts'], indent=2))
