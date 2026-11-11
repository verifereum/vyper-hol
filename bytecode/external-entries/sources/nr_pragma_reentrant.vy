# nonreentrancy-by-default pragma with an @reentrant opt-out and an internal function
#pragma nonreentrancy on
x: uint256

@internal
def g(a: uint256):
    self.x = a

@external
@reentrant
def f(a: uint256):
    self.g(a)

@external
def h() -> uint256:
    return self.x
