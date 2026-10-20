"""Finding 19: extract32 requires a complete 32-byte source window."""

import pytest


CONTRACT = """
@external
@pure
def extract_uint(data: Bytes[64], start: uint256) -> uint256:
    return extract32(data, start, output_type=uint256)

@external
@pure
def extract_byte(data: Bytes[64], start: uint256) -> bytes1:
    return extract32(data, start, output_type=bytes1)
"""


@pytest.mark.parametrize("function", ["extract_uint", "extract_byte"])
def test_short_window_reverts_even_for_narrow_output(get_contract, tx_failed, function):
    contract = get_contract(CONTRACT)
    with tx_failed():
        getattr(contract, function)(b"\x01", 0)


def test_complete_window_is_accepted(get_contract):
    contract = get_contract(CONTRACT)
    data = b"\x01" + bytes(31)
    assert contract.extract_uint(data, 0) == 2**248
    assert contract.extract_byte(data, 0) == b"\x01"
