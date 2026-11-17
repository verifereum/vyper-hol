# two keyword parameters: omit both, or supply the first and omit the second
@internal
def f(x: uint256, y: uint256 = 3, z: uint256 = 5) -> uint256:
    return x * y + z

@external
def omit_both(x: uint256) -> uint256:
    return self.f(x)

@external
def omit_last(x: uint256) -> uint256:
    return self.f(x, 11)
