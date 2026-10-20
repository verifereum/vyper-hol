
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
