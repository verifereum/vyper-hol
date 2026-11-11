struct P:
    l: uint256
    r: uint256

a: P[2]

@external
def f(i: uint256, x: uint256) -> uint256:
    self.a[i].r = x
    return self.a[i].r
