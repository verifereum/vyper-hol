N: constant(uint256) = 1 << 1
M: constant(int256) = (0 - 8) >> 1

@external
@pure
def left(x: int256, n: uint8, values: uint256[N]) -> int256:
    return x << n

@external
@pure
def right(x: int256, n: uint256) -> int256:
    return x >> n

@external
@pure
def count_expression(x: int256, n: uint8) -> int256:
    return x >> (1 + n)
