# 2-D local array literal returned
@external
@pure
def f(a: uint256) -> uint256[2][2]:
    x: uint256[2][2] = [[a, 1], [2, a]]
    return x
