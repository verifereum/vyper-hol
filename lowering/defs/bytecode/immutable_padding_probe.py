#!/usr/bin/env python3
"""Reproduce immutable padding with pinned Vyper and py-evm's Prague VM.

Run with py-evm==0.12.1b1 installed and pass the pinned Vyper Python executable.
This executes constructor bytecode directly; it does not model a CREATE tx.
"""

import argparse
import json
import subprocess
from pathlib import Path

from eth.chains.base import MiningChain
from eth.db.atomic import AtomicDB
from eth.vm.forks.prague import PragueVM
from eth_utils import keccak


COMPILER = '''
import json, sys, warnings
import vyper
from vyper.compiler.settings import Settings, OptimizationLevel
assert vyper.__version__ == "0.5.0a4" and vyper.__commit__ == "cd74ce4f"
with warnings.catch_warnings():
    warnings.simplefilter("ignore")
    result = vyper.compile_code(sys.stdin.read(),
        output_formats=["bytecode", "bytecode_runtime"],
        settings=Settings(optimize=OptimizationLevel.NONE,
                          evm_version="prague", experimental_codegen=True),
        no_bytecode_metadata=True)
print(json.dumps(result))
'''

SOURCE = '''X: immutable(String[40])

@deploy
def __init__({params}):
{body}
    X = "a"

@external
def get() -> String[40]:
    return X
'''


def execute(code, data=b""):
    chain_type = MiningChain.configure(
        __name__="ImmutablePaddingChain", vm_configuration=((0, PragueVM),))
    chain = chain_type.from_genesis(
        AtomicDB(), {"difficulty": 0, "gas_limit": 10_000_000, "timestamp": 1}, {})
    result = chain.get_vm().execute_bytecode(
        origin=b"\x01" * 20, sender=b"\x01" * 20, to=b"\x02" * 20,
        gas_price=0, gas=1_000_000, value=0, data=data, code=code)
    if result.is_error:
        raise RuntimeError(str(result.error))
    return bytes(result.output)


def compile_source(python, source):
    compiled = json.loads(subprocess.check_output(
        [python, "-c", COMPILER], input=source, text=True))
    return tuple(bytes.fromhex(compiled[key].removeprefix("0x"))
                 for key in ("bytecode", "bytecode_runtime"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vyper-python", required=True)
    args = parser.parse_args()
    canonical = (1).to_bytes(32, "big") + b"a" + bytes(63)
    cases = [
        ("clean", "", "", [b""]),
        ("dirty", "", '    b: String[1] = "b"', [b""]),
        ("conditional", "dirty: bool", '    b: String[1] = "b" if dirty else ""',
         [(0).to_bytes(32, "big"), (1).to_bytes(32, "big")]),
    ]
    report = []
    for name, params, body, inputs in cases:
        source = SOURCE.format(params=params, body=body)
        deploy, runtime = compile_source(args.vyper_python, source)
        for constructor_args in inputs:
            installed = execute(deploy + constructor_args)
            assert installed[:len(runtime)] == runtime
            section = installed[len(runtime):]
            assert len(section) == 96
            assert section[:64] == canonical[:64]
            returned = execute(installed, keccak(text="get()")[:4])
            assert returned == (32).to_bytes(32, "big") + canonical[:64]
            report.append(dict(case=name, constructor_args=constructor_args.hex(),
                               deploy_bytes=len(deploy), runtime_bytes=len(runtime),
                               section_hex=section.hex(), canonical=section == canonical,
                               padding_word=int.from_bytes(section[64:], "big"),
                               get="a"))
    assert [row["padding_word"] for row in report] == [0, 1, 0, 1]
    assert [row["canonical"] for row in report] == [True, False, True, False]
    assert report[2]["section_hex"] != report[3]["section_hex"]
    source = Path(__file__).with_name("immutables") / "sources/p23_imm_uint256.vy"
    deploy, runtime = compile_source(args.vyper_python, source.read_text())
    installed = execute(deploy)
    assert installed == runtime + (42).to_bytes(32, "big")
    assert execute(installed, keccak(text="get()")[:4]) == (42).to_bytes(32, "big")
    report.append(dict(case="p23_imm_uint256", deploy_bytes=len(deploy),
                       runtime_bytes=len(runtime), section_bytes=32, get=42))
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
