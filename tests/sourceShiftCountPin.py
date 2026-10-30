#!/usr/bin/env python3
"""Independent VYPER_PIN shift acceptance and Prague execution regression.

Run `.../venv/bin/python -I tests/sourceShiftCountPin.py oracle`, then
`.../evm-venv/bin/python -I tests/sourceShiftCountPin.py execute`.
Shared parser captures are maintained by sourceOrdinaryPin.py.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.agent-files/source-shift-pin.json'


def oracle():
    import vyper
    from vyper.compiler.settings import Settings, OptimizationLevel
    pin = (ROOT / 'VYPER_PIN').read_text().strip()
    checkout = ROOT / '.agent-files/folded-value-validation/vyper-src'
    assert subprocess.check_output(['git', '-C', checkout, 'rev-parse', 'HEAD'], text=True).strip() == pin
    assert pin.startswith(vyper.__commit__)
    package = Path(vyper.__file__).resolve().parent
    # Verify implementation bytes, not just the compiler's commit label.
    for path in package.rglob('*.py'):
        rel = path.relative_to(package)
        reference = checkout / 'vyper' / rel
        assert (reference.exists() and path.read_bytes() == reference.read_bytes()) or str(rel) == 'version.py', rel
    settings = Settings(optimize=OptimizationLevel.NONE, experimental_codegen=True, evm_version='prague')
    rows = []
    for name in ['constant_bound', 'constant_shifts']:
        source = (ROOT / 'tests/fixtures/check_contract' / (name + '.vy')).read_text()
        result = vyper.compile_code(source, settings=settings, no_bytecode_metadata=True,
                                    output_formats=('bytecode_runtime',))
        rows.append(dict(name=name, accepted=True, source=source,
                         source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                         runtime=result['bytecode_runtime']))
    cases = [('int8', 'n', False), ('int256', 'n', False),
             ('uint8', 'n', True), ('uint256', 'n', True),
             ('uint8', '1 + n', True), ('int8', '1 + n', False),
             ('uint8', '(1 - 2) + 2', True), ('uint8', '(256 + 1) - 256', True),
             ('uint8', '-(0 - 1)', False), ('uint8', '1 // 0', False),
             ('uint8', '(1 << 256) >> 255', False)]
    for ty, count, expected in cases:
        source = f'@external\n@pure\ndef f(x: int256, n: {ty}) -> int256:\n    return x << ({count})\n'
        try:
            result = vyper.compile_code(source, settings=settings, no_bytecode_metadata=True,
                                        output_formats=('bytecode_runtime',))
            row = dict(name=f'{ty}:{count}', accepted=True, runtime=result['bytecode_runtime'])
        except Exception as error:
            row = dict(name=f'{ty}:{count}', accepted=False, error=type(error).__name__)
        assert row['accepted'] == expected, row
        rows.append(row)
    OUT.write_text(json.dumps(dict(pin=pin, python=platform.python_version(),
        package=str(package), settings='experimental_codegen/NONE/Prague/no metadata', rows=rows), indent=2) + '\n')
    print(json.dumps(dict(pin=pin, cases=len(rows), accepted=sum(r['accepted'] for r in rows))))


def execute():
    from eth.chains.base import MiningChain
    from eth.db.atomic import AtomicDB
    from eth.vm.forks.prague import PragueVM
    from eth.exceptions import Revert
    from eth_abi import encode
    from eth_utils import keccak
    data = json.loads(OUT.read_text())
    rows = {r['name']: r for r in data['rows']}
    chain = MiningChain.configure(__name__='ShiftCountChain', vm_configuration=((0, PragueVM),))
    cases = [('constant_bound', 'power(uint256,uint256[3])', ['uint256', 'uint256[3]'], [2, [0, 0, 0]], 8),
             ('constant_shifts', 'left(int256,uint8,uint256[2])', ['int256', 'uint8', 'uint256[2]'], [-8, 1, [0, 0]], -16),
             ('constant_shifts', 'right(int256,uint256)', ['int256', 'uint256'], [-8, 1], -4),
             ('constant_shifts', 'count_expression(int256,uint8)', ['int256', 'uint8'], [-8, 1], -2),
             ('constant_shifts', 'count_expression(int256,uint8)', ['int256', 'uint8'], [-8, 255], None),
             ('uint8:(1 - 2) + 2', 'f(int256,uint8)', ['int256', 'uint8'], [-8, 0], -16),
             ('uint8:(256 + 1) - 256', 'f(int256,uint8)', ['int256', 'uint8'], [-8, 0], -16)]
    receipts = []
    for name, sig, types, args, expected in cases:
        vm = chain.from_genesis(AtomicDB(), {'difficulty': 0, 'gas_limit': 10_000_000, 'timestamp': 1}, {}).get_vm()
        result = vm.execute_bytecode(origin=b'\x01'*20, sender=b'\x01'*20, to=b'\x02'*20,
            gas_price=0, gas=1_000_000, value=0, data=keccak(text=sig)[:4] + encode(types, args),
            code=bytes.fromhex(rows[name]['runtime'].removeprefix('0x')))
        if expected is None:
            assert result.is_error and isinstance(result.error, Revert)
        else:
            assert not result.is_error and int.from_bytes(result.output, 'big', signed=True) == expected
        receipts.append(dict(name=name, signature=sig, arguments=args, expected=expected,
            output=result.output.hex(), error=type(result.error).__name__ if result.is_error else None))
    data['executions'] = receipts
    OUT.write_text(json.dumps(data, indent=2) + '\n')
    print('7 Prague executions passed, including uint8 count-expression overflow revert')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['oracle', 'execute'])
    args = parser.parse_args()
    oracle() if args.mode == 'oracle' else execute()
