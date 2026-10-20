"""Prepare independent pinned-Vyper inputs for the #560 witness matrix.

--task imports the named Vyper examples from the issue text once. Subsequent
runs use the retained sources and need no issue file. Rejections are recorded,
not counted as parity matches. This script never invokes the HOL compiler.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from memory_store_witnesses import run

here = Path(__file__).resolve().parent
repo = here.parents[2]
root = here / 'memory-construction-matrix'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--task', type=Path)
args = parser.parse_args()
sources = root / 'sources'
oracle = root / 'oracle'
sources.mkdir(parents=True, exist_ok=True)
oracle.mkdir(parents=True, exist_ok=True)
if args.task:
    examples = re.findall(r'^`([^`]+)`:\s*\n```vyper\n(.*?)\n```',
                          args.task.read_text(), re.M | re.S)
    for name, text in examples:
        (sources / (name + '.vy')).write_text(text + '\n')
pin = (repo / 'VYPER_PIN').read_text().strip()
version = run(['vyper', '--version']).strip()
if not version.endswith('commit.' + pin[:8]):
    raise ValueError((version, pin))
results = {}
for source in sorted(sources.glob('*.vy')):
    name = source.stem
    try:
        raw = oracle / (name + '.raw.json')
        raw.write_text(run(['vyper', '-f', 'annotated_ast,layout', str(source)]))
        run(['python3', str(repo / 'tests/sanitize_check_contract_json.py'),
             str(raw), str(oracle / (name + '.json')), '--replace', str(sources) + '/='])
        raw.unlink()
        deploy, runtime = run(['vyper', '--experimental-codegen', '--evm-version', 'prague',
            '-O', 'none', '--disable-bytecode-metadata', '-f', 'bytecode,bytecode_runtime',
            str(source)]).splitlines()
        (oracle / (name + '.hex')).write_text('deploy=' + deploy.removeprefix('0x')
            + '\nruntime=' + runtime.removeprefix('0x') + '\n')
        results[name] = {'python': 'ACCEPT', 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
    except subprocess.CalledProcessError as error:
        results[name] = {'python': 'REJECT', 'diagnostic': error.stderr}
    print(name, results[name]['python'], flush=True)
(root / 'preparation.json').write_text(json.dumps({'vyper_version': version,
    'vyper_commit': pin, 'settings': {'experimental_codegen': True,
    'optimization_level': 'NONE', 'evm_version': 'prague', 'bytecode_metadata': False},
    'witnesses': results}, indent=2) + '\n')
(root / 'accepted.txt').write_text(''.join(name + '\n' for name in results
    if results[name]['python'] == 'ACCEPT'))
