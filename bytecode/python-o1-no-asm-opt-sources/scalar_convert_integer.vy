@external
@pure
def uint_to_uint(x: uint256) -> uint8:
    return convert(x, uint8)

@external
@pure
def int_to_uint(x: int256) -> uint256:
    return convert(x, uint256)

@external
@pure
def uint_to_int(x: uint256) -> int256:
    return convert(x, int256)

@external
@pure
def bool_to_uint(x: bool) -> uint8:
    return convert(x, uint8)
