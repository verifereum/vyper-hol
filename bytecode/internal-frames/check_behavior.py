"""Execute the internal-local clobber witnesses against a runtime hex directory."""

import argparse
import json
from importlib.metadata import version
from pathlib import Path

from eth.chains.base import MiningChain
from eth.db.atomic import AtomicDB
from eth.vm.forks.prague import PragueVM
from eth_abi import decode, encode
from eth_utils import keccak


def check(label, root):
    chain_type = MiningChain.configure(
        __name__="InternalFramesWitnessChain", vm_configuration=((0, PragueVM),))
    results = []
    for name, expected_storage in [("p39_int_local_clobber", 6),
                                   ("p40_int_for_clobber", 11)]:
        runtime = next(line.removeprefix("runtime=")
                       for line in (root / (name + ".hex")).read_text().splitlines()
                       if line.startswith("runtime="))
        chain = chain_type.from_genesis(
            AtomicDB(), {"difficulty": 0, "gas_limit": 10_000_000,
                         "timestamp": 1}, {})
        vm = chain.get_vm()
        recipient = b"\x02" * 20
        computation = vm.execute_bytecode(
            origin=b"\x01" * 20, sender=b"\x01" * 20,
            to=recipient, gas_price=0, gas=1_000_000, value=0,
            data=keccak(text="foo(uint256)")[:4] + encode(["uint256"], [5]),
            code=bytes.fromhex(runtime))
        if computation.is_error:
            raise ValueError(f"{label} {name}: {computation.error}")
        result = decode(["uint256"], computation.output)[0]
        storage = vm.state.get_storage(recipient, 0)
        if (result, storage) != (5, expected_storage):
            raise ValueError(f"{label} {name}: return={result}, storage={storage}")
        results.append({"witness": name, "return": result, "storage_0": storage,
                        "runtime_bytes": len(bytes.fromhex(runtime))})
    return {"label": label, "root": str(root), "results": results,
            "py_evm": version("py-evm"), "eth_abi": version("eth-abi")}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("label")
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.label, args.root), indent=2))
