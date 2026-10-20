"""Finding 12: widening an address left-pads it as an integer value."""

CONTRACT = """
@external
@pure
def as_bytes21(item: address) -> bytes21:
    return convert(item, bytes21)

@external
@pure
def as_bytes32(item: address) -> bytes32:
    return convert(item, bytes32)

@external
@pure
def widen_bytes(item: bytes20) -> bytes32:
    return convert(item, bytes32)
"""


def test_address_and_fixed_bytes_use_different_widening(get_contract):
    contract = get_contract(CONTRACT)
    address_one = "0x0000000000000000000000000000000000000001"
    bytes_one = bytes(19) + b"\x01"

    assert contract.as_bytes21(address_one) == bytes(20) + b"\x01"
    assert contract.as_bytes32(address_one) == bytes(31) + b"\x01"
    assert contract.widen_bytes(bytes_one) == bytes_one + bytes(12)
