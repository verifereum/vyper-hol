C: constant(uint256[2]) = [10, 20]
x: uint256

@internal
def g() -> uint256:
    self.x = self.x + 1
    return 1

@external
def f(a: uint256 = C[self.g()]) -> uint256:
    return a + self.x
