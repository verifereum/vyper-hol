"""Finding 16: bytes32 supports bitwise and shift binary operators."""

import pytest


CONTRACT = """
@external
@pure
def bit_and(left: bytes32, right: bytes32) -> bytes32:
    return left & right

@external
@pure
def bit_or(left: bytes32, right: bytes32) -> bytes32:
    return left | right

@external
@pure
def bit_xor(left: bytes32, right: bytes32) -> bytes32:
    return left ^ right

@external
@pure
def shift_left(item: bytes32, amount: uint256) -> bytes32:
    return item << amount

@external
@pure
def shift_right(item: bytes32, amount: uint256) -> bytes32:
    return item >> amount
"""


@pytest.mark.parametrize(
    "function,args,expected",
    [
        ("bit_and", (b"\xa5" * 32, b"\x3c" * 32), b"\x24" * 32),
        ("bit_or", (b"\xa5" * 32, b"\x3c" * 32), b"\xbd" * 32),
        ("bit_xor", (b"\xa5" * 32, b"\x3c" * 32), b"\x99" * 32),
        ("shift_left", (b"\xa5" * 32, 8), b"\xa5" * 31 + b"\x00"),
        ("shift_right", (b"\xa5" * 32, 8), b"\x00" + b"\xa5" * 31),
    ],
)
def test_bytes32_binary_operator(get_contract, function, args, expected):
    assert getattr(get_contract(CONTRACT), function)(*args) == expected
