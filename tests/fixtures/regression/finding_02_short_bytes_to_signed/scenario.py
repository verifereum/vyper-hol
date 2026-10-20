"""Finding 2: short byte sequences are sign-extended for signed conversion."""

CONTRACT = """
@external
@pure
def fixed_to_int256(data: bytes1) -> int256:
    return convert(data, int256)

@external
@pure
def fixed_to_int8(data: bytes1) -> int8:
    return convert(data, int8)

@external
@pure
def dynamic_to_int256(data: Bytes[1]) -> int256:
    return convert(data, int256)
"""


def test_short_bytes_use_the_first_byte_as_the_sign_bit(get_contract):
    contract = get_contract(CONTRACT)

    assert contract.fixed_to_int256(b"\xff") == -1
    assert contract.fixed_to_int8(b"\xff") == -1
    assert contract.dynamic_to_int256(b"\xff") == -1
    assert contract.fixed_to_int256(b"\x80") == -128
    assert contract.fixed_to_int256(b"\x7f") == 127
