
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
