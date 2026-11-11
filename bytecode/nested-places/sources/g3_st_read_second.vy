struct P:
    l: uint256
    r: uint256

p: P

@external
def f(x: uint256) -> uint256:
    self.p.r = x
    return self.p.r
