# a01: constant fixed array indexed at runtime
A: constant(uint256[3]) = [10, 20, 30]

@external
def f(i: uint256) -> uint256:
    return A[i]
