#!/usr/bin/env python3
"""Check both independently produced runtimes; never treat behavior as byte parity."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def encode_words(words):
    return b''.join(word.to_bytes(32, 'big') for word in words)


def expected_words(value, dynamic):
    # ABI offsets in a dynamic array exclude its length word.
    offset = 32 * len(value)
    heads, tails = [], []
    for row in value:
        heads.append(offset)
        tail = [len(row), *row]
        tails.extend(tail)
        offset += 32 * len(tail)
    return [32, *([len(value)] if dynamic else []), *heads, *tails]


def require_result(error, actual, expected):
    if error or actual != expected:
        raise ValueError(f'error={error}; return={actual.hex()}; expected={expected.hex()}')


def load_hex(path):
    fields = dict(line.split('=', 1) for line in path.read_text().splitlines()
                  if line and not line.startswith('#'))
    return {key: bytes.fromhex(fields[key]) for key in ('deploy', 'runtime')}


def self_test():
    cases = json.loads((ROOT / 'cases.json').read_text())
    count = 0
    for name, fixture in cases.items():
        assert len(bytes.fromhex(fixture['selector'])) == 4
        for case in fixture['cases']:
            assert expected_words(case['input'], name == 'arr_dyn_of_dyn') == case['words']
            data = encode_words(case['words'])
            require_result(False, data, data)
            for error, wrong in ((True, data), (False, data + b'\x00')):
                try:
                    require_result(error, wrong, data)
                except ValueError:
                    pass
                else:
                    raise AssertionError('negative result check accepted mismatch')
            count += 1
    assert count == 10
    print('PASS: ten ABI vectors; success checks; revert and return-mismatch negative tests')


def execute(runtime, calldata):
    from eth.chains.base import MiningChain
    from eth.db.atomic import AtomicDB
    from eth.vm.forks.prague import PragueVM
    chain_class = MiningChain.configure(__name__='DeepDupValidation',
                                       vm_configuration=((0, PragueVM),))
    chain = chain_class.from_genesis(AtomicDB(),
        {'difficulty': 0, 'gas_limit': 30000000, 'timestamp': 1}, {})
    result = chain.get_vm().execute_bytecode(
        origin=b'\x11' * 20, gas_price=0, gas=20000000,
        to=b'\x22' * 20, sender=b'\x11' * 20, value=0,
        data=calldata, code=runtime)
    if result.is_error:
        print('EVM_ERROR', type(result.error).__name__, str(result.error))
    return result.is_error, bytes(result.output)


def compare(python_dir, hol_dir):
    cases = json.loads((ROOT / 'cases.json').read_text())
    failures = []
    for name, fixture in cases.items():
        python = load_hex(python_dir / (name + '.hex'))
        hol = load_hex(hol_dir / (name + '.hex'))
        # This file pair alone does not establish checker acceptance or provenance.
        for kind in ('deploy', 'runtime'):
            print(name, kind, 'python_bytes=', len(python[kind]), 'hol_bytes=', len(hol[kind]))
            if python[kind] != hol[kind]:
                failures.append(f'{name}: {kind} byte parity failed')
        for index, case in enumerate(fixture['cases']):
            expected = encode_words(case['words'])
            calldata = bytes.fromhex(fixture['selector']) + expected
            for producer, output in (('python', python), ('hol', hol)):
                error, actual = execute(output['runtime'], calldata)
                try:
                    require_result(error, actual, expected)
                except ValueError as failure:
                    message = f'{name} {index} {producer}: {failure}'
                    failures.append(message)
                    print('FAIL', message)
                else:
                    print(name, index, producer, 'PASS', actual.hex())
    if failures:
        raise ValueError('\n'.join(failures))
    print('PASS: deployment/runtime byte equality and ten behavior cases on both runtimes')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--python-dir', type=Path)
    parser.add_argument('--hol-dir', type=Path)
    args = parser.parse_args()
    self_test()
    if not args.self_test:
        if args.python_dir is None or args.hol_dir is None:
            parser.error('comparison requires --python-dir and --hol-dir')
        compare(args.python_dir, args.hol_dir)


if __name__ == '__main__':
    main()
