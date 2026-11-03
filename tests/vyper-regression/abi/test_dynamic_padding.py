"""ABI decoding ignores bytes beyond a dynamic value's declared length."""

CONTRACT = """
@external
@pure
def decode(payload: Bytes[96]) -> Bytes[32]:
    return abi_decode(payload, Bytes[32])
"""


def encoded_single_byte(padding_byte):
    offset_to_value = (32).to_bytes(32, "big")
    declared_length = (1).to_bytes(32, "big")
    padded_value = b"a" + bytes([padding_byte]) + bytes(30)
    return offset_to_value + declared_length + padded_value


def test_nonzero_dynamic_padding_does_not_change_the_decoded_value(get_contract):
    contract = get_contract(CONTRACT)
    assert contract.decode(encoded_single_byte(0xFF)) == b"a"
    assert contract.decode(encoded_single_byte(0x00)) == b"a"
