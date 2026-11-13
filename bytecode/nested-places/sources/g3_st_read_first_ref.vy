struct P:
    l: uint256
    r: uint256

p: P

@external
def f(x: uint256) -> uint256:
    self.p.l = x
    return self.p.l
