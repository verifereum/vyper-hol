# default arg = module constant
K: constant(uint256) = 42

@external
def f(b: uint256 = K) -> uint256:
    return b
