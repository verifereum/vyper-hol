#!/usr/bin/env python3
"""Check the reference Vyper witnesses with py-evm's Prague implementation."""

from pathlib import Path

from eth.chains.base import MiningChain
from eth.db.atomic import AtomicDB
from eth.exceptions import Revert
from eth.vm.forks.prague import PragueVM
from eth_hash.auto import keccak


def word(n):
    return n.to_bytes(32, "big")


def mapping_slot(base, key):
    # Vyper hashes base || key (codegen_venom/expr.py, lower_Subscript).
    return int.from_bytes(keccak(word(base) + word(key)), "big")


def fixtures():
    m0 = lambda key: mapping_slot(0, key)
    m1 = lambda key: mapping_slot(1, key)
    return [
        ("c08_storage_arr_assign_computed_rhs", "f(uint256,uint256)", [0, 7], {},
         False, b"", {0: 8}),
        ("c09_storage_map_assign_computed_rhs", "f(uint256,uint256)", [4, 9], {},
         False, b"", {m0(5): 18}),
        ("g6_write_order_side", "f(uint256)", [3], {1: 8, 3: 1},
         False, b"", {1: 11, 3: 1}),
        ("x04_assign_sideeffect_order", "f()", [], {},
         False, b"", {0: 2, m1(1): 0, m1(2): 1}),
        ("g19_aug_rhs_modifies_target", "f()", [], {}, False, b"", {0: 1}),
        ("x03_assign_elem_from_pop", "f(uint256)", [5], {}, True, b"", {}),
        ("s11_storage_map_assign_extcall_rhs", "f(address,uint256)",
         [int.from_bytes(b"\x22" * 20), 3], {}, False, b"", {m0(3): 7}),
        ("assign_delayed_storage_read", "f()", [], {},
         False, b"", {0: 1, m1(1): 1}),
        ("assign_delayed_popped_read", "f()", [], {},
         False, word(5), {m0(5): 5}),
        ("assign_nested_popped_read", "f()", [], {},
         False, b"", {m0(3): 1, m0(3) + 1: 1}),
        ("aug_storage_shrink", "f()", [], {0: 1, 1: 5},
         False, b"", {0: 0, 1: 10}),
        ("aug_memory_shrink", "f()", [], {}, False, word(0), {}),
        ("aug_memory_shrink_append", "f()", [], {}, False, word(7), {}),
    ]


def main():
    cases = fixtures()
    fixture_dir = Path(__file__).resolve().parent
    chain_type = MiningChain.configure(
        "AssignmentOrderChain", vm_configuration=((0, PragueVM),), chain_id=1)
    target, sender, helper = b"\x11" * 20, b"\x33" * 20, b"\x22" * 20
    passed_all = True
    for name, signature, arguments, initial, reverted, returned, expected in cases:
        fields = dict(line.split("=", 1) for line in
                      (fixture_dir / "oracle" / (name + ".hex")).read_text().splitlines()
                      if line and not line.startswith("#"))
        runtime = bytes.fromhex(fields["runtime"])
        chain = chain_type.from_genesis(
            AtomicDB(), {"difficulty": 0, "gas_limit": 30_000_000,
                         "timestamp": 1, "base_fee_per_gas": 0},
            {target: {"balance": 0, "nonce": 1, "code": runtime, "storage": initial},
             sender: {"balance": 10**20, "nonce": 0, "code": b"", "storage": {}},
             # External g() returns 7; its ABI selector is irrelevant to this stub.
             helper: {"balance": 0, "nonce": 1,
                      "code": bytes.fromhex("600760005260206000f3"), "storage": {}}})
        vm = chain.get_vm()
        calldata = keccak(signature.encode())[:4] + b"".join(map(word, arguments))
        computation = vm.execute_bytecode(
            origin=sender, gas_price=0, gas=10_000_000, to=target,
            sender=sender, value=0, data=calldata, code=runtime, code_address=target)
        observed = {slot: vm.state.get_storage(target, slot) for slot in expected}
        is_revert = computation.is_error and isinstance(computation.error, Revert)
        passed = (computation.is_error == reverted and is_revert == reverted and
                  computation.output == returned and observed == expected)
        passed_all = passed_all and passed
        print(f"{name}: {'PASS' if passed else 'FAIL'}")
    if not passed_all:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
