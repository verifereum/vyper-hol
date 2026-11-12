# internal function with a terminating revert branch (no strings) and stack params live at the branch
@internal
def f(y: uint256, z: uint256) -> uint256:
    if y == 3:
        raise
    return y + z

@external
def foo(x: uint256) -> uint256:
    return self.f(x, 1)
