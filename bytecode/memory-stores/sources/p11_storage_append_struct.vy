struct S:
    a: uint256
    b: uint256
d: DynArray[S, 3]
@external
def f(x: uint256) -> uint256:
    self.d.append(S(a=x, b=2))
    return self.d[0].a
