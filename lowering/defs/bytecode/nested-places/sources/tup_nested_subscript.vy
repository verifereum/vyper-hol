@external
@pure
def f(a: uint256) -> uint256:
    t: (uint256, (uint256, uint256)) = (a, (a + 1, a + 2))
    return t[1][1]
