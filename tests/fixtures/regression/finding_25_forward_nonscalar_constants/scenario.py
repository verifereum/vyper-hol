"""Finding 25: non-scalar constants may refer to later declarations."""

import pytest


BYTES = """
FIRST: constant(Bytes[3]) = SECOND
SECOND: constant(Bytes[3]) = b"abc"
@external
@pure
def value() -> Bytes[3]:
    return FIRST
"""

STRING = """
FIRST: constant(String[3]) = SECOND
SECOND: constant(String[3]) = "abc"
@external
@pure
def value() -> String[3]:
    return FIRST
"""

ARRAY = """
FIRST: constant(uint256[2]) = SECOND
SECOND: constant(uint256[2]) = [3, 7]
@external
@pure
def value() -> uint256[2]:
    return FIRST
"""


@pytest.mark.parametrize(
    "source,expected",
    [(BYTES, b"abc"), (STRING, "abc"), (ARRAY, [3, 7])],
    ids=["bytes", "string", "array"],
)
def test_forward_constant_reference(get_contract, source, expected):
    assert get_contract(source).value() == expected
