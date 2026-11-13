a: transient(uint256[3])

@external
def f(i: uint256, x: uint256) -> uint256:
    self.a[i] = x
    return self.a[i]
