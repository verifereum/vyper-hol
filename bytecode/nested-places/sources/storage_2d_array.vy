a: uint256[2][3]

@external
def f(i: uint256, j: uint256, x: uint256) -> uint256:
    self.a[i][j] = x
    return self.a[i][j]
