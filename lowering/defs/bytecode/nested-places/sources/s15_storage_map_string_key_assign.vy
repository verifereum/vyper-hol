m: HashMap[String[10], uint256]

@external
def f(s: String[10], x: uint256) -> uint256:
    self.m[s] = x
    return self.m[s]
