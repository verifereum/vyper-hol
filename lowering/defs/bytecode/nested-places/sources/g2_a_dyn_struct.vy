struct P:
    l: uint256
    r: uint256

d: DynArray[P, 3]

@external
def f(x: uint256) -> uint256:
    self.d.append(P(l=1, r=x))
    return self.d[0].r
