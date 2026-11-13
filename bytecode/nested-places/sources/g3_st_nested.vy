struct P:
    l: uint256
    r: uint256

struct S:
    k: uint256
    inner: P

s: S

@external
def f(x: uint256) -> uint256:
    self.s.inner.r = x
    return self.s.inner.r
