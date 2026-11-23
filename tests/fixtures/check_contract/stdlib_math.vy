import math


@external
@pure
def root(x: uint256) -> uint256:
    return math.isqrt(x)
