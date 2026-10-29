m: HashMap[uint256, uint256]

@external
def f(k: uint256) -> uint256:
    self.m[k] += 1
    return self.m[k]
