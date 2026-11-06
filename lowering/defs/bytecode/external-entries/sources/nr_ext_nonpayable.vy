x: uint256

@external
@nonreentrant
def f(a: uint256) -> uint256:
    self.x = a
    return a + 1
