# internal -> internal call chain
@internal
def g(y: uint256) -> uint256:
    return y + 1

@internal
def f(y: uint256) -> uint256:
    return self.g(y)

@external
def foo(x: uint256) -> uint256:
    return self.f(x)
