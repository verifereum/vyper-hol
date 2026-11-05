A: constant(uint256[3]) = [10, 20, 30]

@external
def f() -> uint256[3]:
    a: uint256[3] = A
    return a
