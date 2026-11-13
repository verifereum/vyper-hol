m: HashMap[uint256, uint8]

@external
def f(k: uint256, x: uint8) -> uint8:
    self.m[k] = x
    return self.m[k]
