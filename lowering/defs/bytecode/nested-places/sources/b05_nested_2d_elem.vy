# a11: nested memory target a[i][j] = x on a 2D local array
@external
def f(i: uint256, j: uint256, x: uint256) -> uint256:
    a: uint256[2][2] = [[1, 2], [3, 4]]
    a[i][j] = x
    return a[1][1]
