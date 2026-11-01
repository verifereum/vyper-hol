m: transient(HashMap[uint256, uint256])

@external
def f(k: uint256, x: uint256) -> uint256:
    self.m[k] = x
    return self.m[k]
