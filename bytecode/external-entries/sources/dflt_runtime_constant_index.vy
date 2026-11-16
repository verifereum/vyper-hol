struct S:
    x: uint256

A: constant(S[2]) = [S(x=123), S(x=456)]

@external
def f(a: uint256 = A[block.number % 2].x) -> uint256:
    return a
