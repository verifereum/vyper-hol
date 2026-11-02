x: uint256

@internal
@nonreentrant
def g(a: uint256) -> uint256:
    self.x = a
    return a

@external
def f(a: uint256) -> uint256:
    first: uint256 = self.g(a)
    return first + self.g(a)
