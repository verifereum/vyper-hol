d: uint256[2][2]

@internal
def rewrite() -> uint256:
    self.d[0][1] = 7
    return 1

@external
def f() -> uint256:
    self.d = [[0, 1], [0, 0]]
    return self.d[0][self.rewrite()]
