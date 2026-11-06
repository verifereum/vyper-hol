# internal call omitting a word default, and the same call supplying it
@internal
def f(x: uint256, y: uint256 = 7) -> uint256:
    return x + y

@external
def omit(x: uint256) -> uint256:
    return self.f(x)

@external
def supply(x: uint256) -> uint256:
    return self.f(x, 1)
