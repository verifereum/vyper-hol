# a01: constant used as a default argument value
D: constant(uint256) = 9

@external
def f(a: uint256 = D) -> uint256:
    return a
