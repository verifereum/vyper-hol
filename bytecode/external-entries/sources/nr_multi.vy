x: uint256

@external
@nonreentrant
def f(a: uint256):
    self.x = a

@external
@nonreentrant
def g() -> uint256:
    return self.x
