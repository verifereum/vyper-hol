"""External calls ignore unused dynamic Bytes/String returndata padding."""

import pytest


RAW_RETURN = """
@external
@pure
@raw_return
def get(payload: Bytes[96]) -> Bytes[96]:
    return payload
"""


@pytest.mark.parametrize("return_type, expected", [("Bytes[32]", b"a"), ("String[32]", "a")])
def test_external_call_ignores_dynamic_padding(get_contract, tx_failed, return_type, expected):
    callee = get_contract(RAW_RETURN)
    caller = get_contract(f"""
interface Provider:
    def get(payload: Bytes[96]) -> {return_type}: view

@external
@view
def decode(target: address, payload: Bytes[96]) -> {return_type}:
    return staticcall Provider(target).get(payload)
""")
    head = (32).to_bytes(32, "big") + (1).to_bytes(32, "big")
    assert caller.decode(callee.address, head + b"a" + b"\xff" * 31) == expected
    assert caller.decode(callee.address, head + b"a" + bytes(31)) == expected

    # Relaxing padding must not accept missing bytes within the declared value.
    head = (32).to_bytes(32, "big") + (2).to_bytes(32, "big")
    with tx_failed():
        caller.decode(callee.address, head + b"a")
