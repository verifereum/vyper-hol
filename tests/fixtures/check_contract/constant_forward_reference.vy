# A constant may refer to one declared after it.
Z: constant(uint256) = Y + 1
Y: constant(uint256) = empty(uint256) + 1

@external
@pure
def f() -> uint256:
    return Z
