"""Finding 18: missing calldata words read as zero beyond the finite input."""

import pytest


CONTRACT = """
@external
@pure
def echo(data: Bytes[64]) -> Bytes[64]:
    return data
"""


@pytest.mark.parametrize("offset", [128, 4096])
def test_missing_dynamic_length_word_is_zero_extended(get_contract, env, keccak, offset):
    contract = get_contract(CONTRACT)
    selector = keccak(b"echo(bytes)")[:4]
    calldata = selector + offset.to_bytes(32, "big")

    assert env.message_call(contract.address, data=calldata) == (
        (32).to_bytes(32, "big") + bytes(32)
    )
