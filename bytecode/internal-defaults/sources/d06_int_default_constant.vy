# An omitted default must use the substituted module constant.
DEFAULT_VALUE: constant(uint256) = 7

@internal
def f(x: uint256, y: uint256 = DEFAULT_VALUE) -> uint256:
    return x + y

@external
def omit(x: uint256) -> uint256:
    return self.f(x)

@external
def supply(x: uint256) -> uint256:
    return self.f(x, 1)
