#!/usr/bin/env python3
"""Execute issue #551 regression cases against independent and HOL runtimes."""

from __future__ import annotations

import argparse
import hashlib
import json
from importlib.metadata import version
from pathlib import Path

from eth.chains.base import MiningChain
from eth.db.atomic import AtomicDB
from eth.vm.forks.prague import PragueVM
from eth_abi import encode
from eth_utils import keccak

from memory_store_witnesses import read_runtime


def cases():
    def call(stem, signature, types, args, result_types, results, label="canonical"):
        return (stem, label, keccak(text=signature)[:4] + encode(types, args),
                encode(result_types, results))

    yield call("arr_string_arg", "f(string[])", ["string[]"], [["ab"]],
               ["uint256"], [1])
    yield call("arr_string_arg", "f(string[])", ["string[]"], [[]],
               ["uint256"], [0], "empty")
    yield call("arr_string_ret", "f(string[])", ["string[]"], [["ab", "cde"]],
               ["string[]"], [["ab", "cde"]])
    yield call("arr_dyn_of_fixed", "f(uint256[2][])", ["uint256[2][]"],
               [[[1, 2], [3, 4]]], ["uint256[2][]"], [[[1, 2], [3, 4]]])
    yield call("enc_multi", "f(uint256,address)", ["uint256", "address"],
               [5, b"\0" * 19 + b"\x07"], ["bytes"],
               [encode(["uint256", "address"], [5, b"\0" * 19 + b"\x07"])])
    for label, payload, expected in [
        ("canonical", encode(["bytes"], [b"ab"]), encode(["bytes"], [b"ab"])),
        ("empty", encode(["bytes"], [b""]), encode(["bytes"], [b""])),
        ("short", b"", None),
        ("bare-bytes", encode(["bytes"], [b"ab"])[32:], None),
        ("offset-past-end", (256).to_bytes(32, "big") + b"\0" * 64, None),
        ("oversized-value", encode(["bytes"], [b"x" * 33]), None),
    ]:
        yield ("dec_bytes_unwrapT", label,
               keccak(text="f(bytes)")[:4] + encode(["bytes"], [payload]), expected)
    yield call("flag256_arg", "f(uint256)", ["uint256"], [2**256 - 1],
               ["uint256"], [2**256 - 1])
    yield call("flag256_array_arg", "f(uint256[])", ["uint256[]"],
               [[0, 2**255, 2**256 - 1]], ["uint256"], [3])
    yield ("st_string_field_arg", "wrapped-calldata-offset",
           keccak(text="f((uint256,string))")[:4] +
           b"".join(n.to_bytes(32, "big") for n in [64, 1, 77, 2**256 - 32]),
           encode(["uint256"], [77]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--oracle", type=Path, required=True)
    parser.add_argument("--hol", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    chain_type = MiningChain.configure(
        __name__="AbiCodegenWitnessChain", vm_configuration=((0, PragueVM),))
    results = []
    for stem, label, calldata, expected in cases():
        observations = []
        for compiler, root in [("Vyper", args.oracle), ("HOL", args.hol)]:
            code = read_runtime(root / (stem + ".hex"))
            chain = chain_type.from_genesis(
                AtomicDB(), {"difficulty": 0, "gas_limit": 10_000_000,
                             "timestamp": 1}, {})
            computation = chain.get_vm().execute_bytecode(
                origin=b"\x01" * 20, sender=b"\x01" * 20, to=b"\x02" * 20,
                gas_price=0, gas=1_000_000, value=0, data=calldata, code=code)
            reverted = computation.is_error
            # Invalid opcodes and VM failures are not successful decoder reverts.
            if expected is None:
                passed = reverted and type(computation.error).__name__ == "Revert"
            else:
                passed = not reverted and computation.output == expected
            observations.append({
                "compiler": compiler, "runtime_sha256": hashlib.sha256(code).hexdigest(),
                "reverted": reverted, "output": computation.output.hex(),
                "error": str(computation.error) if reverted else None, "passed": passed,
            })
        passed = all(result["passed"] for result in observations)
        results.append({"fixture": stem, "case": label, "calldata": calldata.hex(),
                        "expected": expected.hex() if expected is not None else "REVERT",
                        "passed": passed, "observations": observations})
        print(stem, label, "PASS" if passed else "FAIL", flush=True)
    receipt = {"oracle": str(args.oracle), "hol": str(args.hol),
               "py_evm": version("py-evm"), "eth_abi": version("eth-abi"),
               "fork": "Prague", "cases": results}
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    if not all(result["passed"] for result in results):
        raise SystemExit("ABI codegen behavior regression failed")


if __name__ == "__main__":
    main()
