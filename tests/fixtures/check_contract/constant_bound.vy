N: constant(uint256) = 1 + 2

@external
@pure
def power(x: uint256, values: uint256[N]) -> uint256:
    return x ** N
