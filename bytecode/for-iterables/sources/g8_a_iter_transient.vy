a: transient(uint256[2])

@external
def f(x: uint256) -> uint256:
    self.a = [x, 3]
    s: uint256 = 0
    for v: uint256 in self.a:
        s += v
    return s
