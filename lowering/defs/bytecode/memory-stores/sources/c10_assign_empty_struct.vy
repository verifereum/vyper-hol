struct S:
    a: uint256
    b: uint256
@external
def f(x: uint256) -> uint256:
    s: S = S(a=x, b=x)
    s = empty(S)
    return s.b
