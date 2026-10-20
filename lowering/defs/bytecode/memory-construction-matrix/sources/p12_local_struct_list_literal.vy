struct S:
    a: uint256
    b: uint256
@external
def f(x: uint256) -> uint256:
    d: DynArray[S, 3] = [S(a=x, b=2)]
    return d[0].a
