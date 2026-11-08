d: DynArray[DynArray[uint256, 2], 2]
x: uint256[2]

@internal
def rewrite() -> uint256:
    self.d[0][0] = 7
    return 0

@external
def f() -> uint256:
    self.d = [[1, 2]]
    self.x[self.rewrite()] = self.d[0][0]
    return self.x[0]
