struct P:
    l: uint256
    r: uint256

p: P

@external
def f(x: uint256) -> uint256:
    if self.p.r > x:
        return self.p.l + self.p.r
    return x
