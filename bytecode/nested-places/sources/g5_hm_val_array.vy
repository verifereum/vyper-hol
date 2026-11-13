# HashMap value fixed array: self.m[k][i]
m: HashMap[uint256, uint256[3]]

@external
def f(k: uint256, i: uint256, x: uint256) -> uint256:
    self.m[k][i] = x
    return self.m[k][i]
