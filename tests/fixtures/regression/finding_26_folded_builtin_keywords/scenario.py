"""Finding 26: compile-time builtin keywords accept folded constant expressions."""

import pytest


DENOMINATION = """
UNIT: constant(String[5]) = "ether"

@external
@pure
def named(amount: uint256) -> uint256:
    return as_wei_value(amount, UNIT)

@external
@pure
def literal(amount: uint256) -> uint256:
    return as_wei_value(amount, "ether")
"""

METHOD_ID = """
@external
@pure
def encoded() -> Bytes[36]:
    return abi_encode(convert(7, uint256), method_id=method_id("foo()"))
"""

ENSURE_TUPLE = """
@external
@pure
def encoded() -> Bytes[96]:
    return abi_encode(b"a", ensure_tuple=not True)
"""


def test_named_denomination_uses_the_constant_value(get_contract):
    contract = get_contract(DENOMINATION)
    assert contract.named(2) == 2 * 10**18
    assert contract.named(2) == contract.literal(2)


def test_named_denomination_preserves_scaled_overflow(get_contract, tx_failed):
    contract = get_contract(DENOMINATION)
    amount = (2**256 - 1) // 10**18 + 1
    with tx_failed():
        contract.named(amount)


@pytest.mark.parametrize(
    "source,expected",
    [
        (METHOD_ID, bytes.fromhex("c2985578") + (7).to_bytes(32, "big")),
        (ENSURE_TUPLE, (1).to_bytes(32, "big") + b"a" + bytes(31)),
    ],
    ids=["nested-method-id", "folded-ensure-tuple"],
)
def test_folded_abi_keyword(get_contract, source, expected):
    assert get_contract(source).encoded() == expected
