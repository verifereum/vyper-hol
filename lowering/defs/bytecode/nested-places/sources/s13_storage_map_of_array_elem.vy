m: HashMap[uint256, uint256[3]]

@external
def f(k: uint256, i: uint256, x: uint256):
    self.m[k][i] = x
