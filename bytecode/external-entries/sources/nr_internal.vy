x: uint256

@internal
@nonreentrant
def g(a: uint256):
    self.x = a

@external
def f(a: uint256):
    self.g(a)
