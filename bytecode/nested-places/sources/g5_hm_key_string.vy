m: HashMap[String[10], uint256]

@external
def f(k: String[10], x: uint256) -> uint256:
    self.m[k] = x
    return self.m[k]
