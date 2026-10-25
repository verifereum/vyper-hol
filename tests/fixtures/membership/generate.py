"""Supply G0006's independent compiler artifacts without starting Alan.

Run with the isolated, constrained Python 3.11.11 oracle environment:
  /tmp/issue-548-vyper-oracle/venv/bin/python -I .agent-files/c6-validation/generate.py
"""
from pathlib import Path
import hashlib
from importlib.metadata import version
import json
import platform
import re
import subprocess
import sys

import vyper
from vyper.compiler.settings import OptimizationLevel
from vyper.venom import OPTIMIZATION_PASSES

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
CHECKOUT = Path('/home/lukasz/vyper')
REQUIRED = ('in_lit_list', 'notin_lit_list3', 'in_mem_dynarray',
            'in_storage_dynarray', 'eq_string_lit_same', 'eq_bytes_storage_both')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    pin = (REPO / 'VYPER_PIN').read_text().strip()
    assert platform.python_version() == '3.11.11'
    assert pin.startswith(vyper.__commit__.strip())
    assert subprocess.check_output(['git', '-C', str(CHECKOUT), 'rev-parse', 'HEAD'], text=True).strip() == pin
    assert not subprocess.check_output(['git', '-C', str(CHECKOUT), 'status', '--porcelain', '--untracked-files=all'], text=True)
    assert OPTIMIZATION_PASSES[OptimizationLevel.NONE] == OPTIMIZATION_PASSES[OptimizationLevel.O1]
    dependencies = {p: version(p) for p in ('cbor2', 'immutables', 'lark', 'packaging', 'pycryptodome', 'wheel')}
    assert list(dependencies.values()) == ['5.9.0', '0.21', '1.1.9', '26.3', '3.23.0', '0.48.0']
    installed = Path(vyper.__file__).parent
    hashes = {}
    for source in sorted((CHECKOUT / 'vyper').rglob('*.py')):
        rel = source.relative_to(CHECKOUT / 'vyper')
        if str(rel) == 'version.py':
            continue  # Untracked setuptools_scm build output; commit checked above.
        assert digest(source) == digest(installed / rel), str(rel)
        hashes[str(rel)] = digest(source)
    audit = {'checkout': str(CHECKOUT), 'commit': pin, 'clean': True,
             'installed_module': str(installed), 'python_source_sha256': hashes,
             'generated_version_file': {'checkout': (CHECKOUT / 'vyper/version.py').read_text(), 'installed': (installed / 'version.py').read_text()}}
    (ROOT / 'compiler-source-audit.json').write_text(json.dumps(audit, indent=2) + '\n')
    for directory in ('sources', 'compiler', 'inputs'):
        (ROOT / directory).mkdir(exist_ok=True)
    task = (REPO / '.agent-files/TASK.md').read_text()
    section = task.split('### Witness sources', 1)[1].split('### Validation procedure', 1)[0]
    sources = dict(re.findall(r'`(\w+)`:\s*```vyper\n(.*?)```', section, re.S))
    sources.update({
        'list_in_lit': '@external\n@pure\ndef f(x: uint256) -> bool:\n    return x in [1, 2, 3]\n',
        'in_dynarray_arg': '@external\ndef f(x: uint256, a: DynArray[uint256, 5]) -> bool:\n    return x in a\n',
        'in_flag': 'flag F:\n    A\n    B\n@external\ndef f(x: F, y: F) -> bool:\n    return x in y\n',
        'notin_flag': 'flag F:\n    A\n    B\n@external\ndef f(x: F) -> bool:\n    return x not in (F.A | F.B)\n',
    })
    # Preserve the lane's six exact input files, including their comments.
    for name in REQUIRED:
        sources[name] = (REPO / 'lowering/defs/bytecode/python-o1-no-asm-opt-sources' / (name + '.vy')).read_text()
    records = {}
    for name, content in sorted(sources.items()):
        source = ROOT / 'sources' / (name + '.vy')
        source.write_text(content)
        record = {'source_sha256': digest(source)}
        for mode, flags in [('ast', ['-f', 'annotated_ast,layout']),
                            ('bytecode', ['--experimental-codegen', '--evm-version', 'prague', '-O', 'none', '--disable-bytecode-metadata', '-f', 'bytecode,bytecode_runtime'])]:
            command = [sys.executable, '-I', '-m', 'vyper', *flags, str(source)]
            result = subprocess.run(command, text=True, capture_output=True)
            output = ROOT / 'compiler' / (name + '.' + mode + '.stdout')
            output.write_text(result.stdout)
            (ROOT / 'compiler' / (name + '.' + mode + '.stderr')).write_text(result.stderr)
            record[mode] = {'command': command, 'exit_code': result.returncode}
            if result.returncode:
                continue
            if mode == 'ast':
                subprocess.run([sys.executable, '-I', str(REPO / 'tests/sanitize_check_contract_json.py'), str(output), str(ROOT / 'inputs' / (name + '.json')), '--replace', str(ROOT / 'sources') + '/='], check=True)
            else:
                deploy, runtime = [line.removeprefix('0x') for line in result.stdout.splitlines()]
                for field in (deploy, runtime):
                    assert field and len(field) % 2 == 0 and re.fullmatch('[0-9a-f]+', field)
                (ROOT / 'compiler' / (name + '.hex')).write_text(f'deploy={deploy}\nruntime={runtime}\n')
                record['outputs'] = {key: {'bytes': len(bytes.fromhex(value)), 'sha256': hashlib.sha256(bytes.fromhex(value)).hexdigest()} for key, value in [('deploy', deploy), ('runtime', runtime)]}
        records[name] = record
        print(name, 'ast=', record['ast']['exit_code'], 'bytecode=', record['bytecode']['exit_code'], flush=True)
    assert len(records) == 30, len(records)
    assert all(records[n][m]['exit_code'] == 0 for n in REQUIRED for m in ('ast', 'bytecode'))
    provenance = {'producer': 'independent pinned Python Vyper', 'compiler_commit': pin,
                  'python_version': platform.python_version(), 'compiler_version': vyper.__version__,
                  'compiler_module': str(installed), 'dependencies': dependencies,
                  'settings': {'experimental_codegen': True, 'optimization': 'NONE', 'venom_pipeline': 'O1', 'final_assembly_optimization': False, 'evm_version': 'prague', 'bytecode_metadata': False},
                  'task_sha256': digest(REPO / '.agent-files/TASK.md'), 'witnesses': records}
    (ROOT / 'compiler-provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    rejected = [n for n, r in records.items() if r['bytecode']['exit_code']]
    assert rejected == ['in_nested_array', 'in_string_list', 'in_struct_dynarray'], rejected
    report = {'request_id': 'G0006', 'lane_id': 'L0009', 'component_uid': 'cmp_13aaf40ccf6a4d05',
              'witnesses': len(records), 'annotated_ast_layout_inputs': len(list((ROOT / 'inputs').glob('*.json'))),
              'deploy_runtime_pairs': len(records) - len(rejected), 'real_compiler_rejections': rejected,
              'required_fixtures_supplied': list(REQUIRED), 'run_started': False,
              'hol_comparison_performed': False, 'completion_credit': False,
              'next_work': 'All independent C6 compiler inputs are supplied. The lane can run the checked HOL comparisons and wire parity theorems using read_file and holbuild. Existing C2 behavior evidence remains in .agent-files/bytecode-validation. Audit closure and preserve explicit #549/#560 residual labels. No MATCH is claimed by this artifact supply.'}
    (ROOT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    manifest = {str(p.relative_to(ROOT)): digest(p) for p in sorted(ROOT.rglob('*')) if p.is_file() and p.name not in ('artifact-sha256.json', 'release.json', 'lane-before-release.json', 'release.py')}
    (ROOT / 'artifact-sha256.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
