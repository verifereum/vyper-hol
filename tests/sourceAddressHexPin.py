#!/usr/bin/env python3
"""Pin-verified acceptance plus real pre-erasure address/bytes20 captures."""
import argparse
import hashlib
import json
from pathlib import Path
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FIX = ROOT / 'tests/sourceAddressHexFixtures'
LOWER = '0xabcdefabcdefabcdefabcdefabcdefabcdefabcd'
CHECK = '0xABcdEFABcdEFabcdEfAbCdefabcdeFABcDEFabCD'
ZERO = '0x' + '00' * 20


def main(generate):
    import vyper
    from vyper.utils import checksum_encode
    pin = (ROOT / 'VYPER_PIN').read_text().strip()
    checkout = ROOT / '.agent-files/folded-value-validation/vyper-src'
    assert subprocess.check_output(['git', '-C', checkout, 'rev-parse', 'HEAD'], text=True).strip() == pin
    assert not subprocess.check_output(['git', '-C', checkout, 'status', '--porcelain'])
    assert pin.startswith(vyper.__commit__)
    package = Path(vyper.__file__).resolve().parent
    for path in package.rglob('*.py'):
        ref = checkout / 'vyper' / path.relative_to(package)
        assert (ref.exists() and path.read_bytes() == ref.read_bytes()) or path.name == 'version.py', path
    assert checksum_encode(LOWER) == CHECK
    capture = runpy.run_path(str(ROOT / 'tests/fixtures/check_contract/source_syntax/generate.py'))['retained']
    def source(ty, expr, params=''):
        return f'@external\n@pure\ndef f({params}) -> {ty}:\n    return {expr}\n'
    cases = [('address_bytes20', (ROOT / 'tests/fixtures/check_contract/address_bytes20.vy').read_text(), True),
             ('bytes20_address', source('address', 'convert(a, address)', 'a: bytes20'), True),
             ('address_checksum', source('address', CHECK), True),
             ('address_zero', source('address', ZERO), True),
             ('bytes20_lower', source('bytes20', LOWER), True),
             ('bytes20_upper', source('bytes20', LOWER.upper().replace('0X', '0x')), True),
             ('address_bad_checksum', source('address', LOWER), False),
             ('bytes20_mixed', source('bytes20', CHECK), False),
             ('address_short', source('address', '0x1234'), False),
             ('bytes20_short', source('bytes20', '0x1234'), False),
             ('convert_checksum', source('bytes20', f'convert({CHECK}, bytes20)'), True),
             ('convert_lower_address', source('address', f'convert({LOWER}, address)'), True),
             ('convert_same_address', source('address', f'convert({CHECK}, address)'), False),
             ('convert_same_bytes20', source('bytes20', f'convert({LOWER}, bytes20)'), False),
             ('constant_bytes20_address', f'C: constant(bytes20) = {ZERO}\n' + source('address', 'convert(C, address)'), True),
             ('constant_address_bytes20', f'C: constant(address) = {ZERO}\n' + source('bytes20', 'convert(C, bytes20)'), True),
             ('constant_same_address', f'C: constant(address) = {ZERO}\n' + source('address', 'convert(C, address)'), False),
             ('constant_same_bytes20', f'C: constant(bytes20) = {ZERO}\n' + source('bytes20', 'convert(C, bytes20)'), False)]
    rows = []
    for name, text, expected in cases:
        try:
            result = vyper.compile_code(text, output_formats=('bytecode_runtime',))
            accepted, error = True, None
        except Exception as exc:
            accepted, error = False, type(exc).__name__
        assert accepted == expected, (name, accepted, error)
        data = json.dumps(capture(text, name), sort_keys=True, separators=(',', ':')) + '\n'
        path = FIX / (name + '.json')
        if generate:
            FIX.mkdir(parents=True, exist_ok=True)
            path.write_text(data)
        else:
            assert path.read_text() == data, path
        row = dict(name=name, accepted=accepted, error=error, source=text,
                   sha256=hashlib.sha256(text.encode()).hexdigest())
        rows.append(row)
    out = ROOT / '.agent-files/source-address-hex-pin.json'
    out.write_text(json.dumps(dict(pin=pin, rows=rows), indent=2) + '\n')
    print(f'{len(rows)} independently pinned address/hex cases passed')


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--generate', action='store_true')
    main(p.parse_args().generate)
