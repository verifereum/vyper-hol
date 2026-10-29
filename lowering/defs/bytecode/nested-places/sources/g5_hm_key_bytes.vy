m: HashMap[Bytes[40], uint256]

@external
def f(k: Bytes[40], x: uint256) -> uint256:
    self.m[k] = x
    return self.m[k]
