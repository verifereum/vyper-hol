struct P:
    l: uint256
    r: uint256

m: HashMap[uint256, P]

@external
def f(k: uint256, x: uint256) -> uint256:
    self.m[k].r = x
    return self.m[k].r
