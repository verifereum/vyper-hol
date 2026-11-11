# internal function containing assert and raise
@internal
def f(y: uint256) -> uint256:
    assert y != 3, "three"
    if y == 4:
        raise "four"
    return y

@external
def foo(x: uint256) -> uint256:
    return self.f(x)
