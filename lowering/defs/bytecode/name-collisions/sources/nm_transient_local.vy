# local named like a transient variable (#557, a04-03)
t: transient(uint256)

@external
def f() -> uint256:
    self.t = 3
    t: uint256 = 4
    return self.t * t
