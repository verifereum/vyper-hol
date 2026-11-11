# pragma nonreentrancy on
x: uint256

@external
def f(a: uint256):
    self.x = a

@external
@view
def g() -> uint256:
    return self.x
