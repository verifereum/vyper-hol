# internal function with a local initialised from another internal call
@internal
def g(y: uint256) -> uint256:
    return y + 1

@internal
def f(y: uint256) -> uint256:
    z: uint256 = self.g(y)
    return z * 2

@external
def foo(x: uint256) -> uint256:
    return self.f(x)
