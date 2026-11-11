struct S:
    a: uint256
    b: uint256
@external
def f(x: uint256) -> uint256:
    d: DynArray[S, 3] = []
    s: S = S(a=x, b=2)
    d.append(s)
    return d[0].b
