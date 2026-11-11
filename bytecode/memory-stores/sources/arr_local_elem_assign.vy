@external
@pure
def f(a: uint256) -> uint256[3]:
    x: uint256[3] = empty(uint256[3])
    x[1] = a
    return x
