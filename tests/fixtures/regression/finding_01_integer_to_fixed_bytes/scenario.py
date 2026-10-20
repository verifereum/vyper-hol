"""Finding 1: integer-to-fixed-bytes conversion keeps the low-order bytes."""

CONTRACT = """
@external
@pure
def uint8_to_bytes1(number: uint8) -> bytes1:
    return convert(number, bytes1)

@external
@pure
def uint16_to_bytes2(number: uint16) -> bytes2:
    return convert(number, bytes2)

@external
@pure
def int8_to_bytes1(number: int8) -> bytes1:
    return convert(number, bytes1)
"""


def test_integer_bytes_are_not_taken_from_the_zero_or_sign_extended_end(get_contract):
    contract = get_contract(CONTRACT)

    assert contract.uint8_to_bytes1(1) == b"\x01"
    assert contract.uint16_to_bytes2(0x1234) == b"\x12\x34"
    assert contract.int8_to_bytes1(-128) == b"\x80"
    assert contract.int8_to_bytes1(-1) == b"\xff"
