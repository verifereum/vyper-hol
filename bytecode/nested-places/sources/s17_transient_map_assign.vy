t: transient(HashMap[uint256, uint256])

@external
def f(k: uint256, x: uint256) -> uint256:
    self.t[k] = x
    return self.t[k]
