# a11: read and compute the RHS before resolving the storage target.
a: uint256[3]
i: uint256

@external
def f(x: uint256):
    self.a[self.i] = self.a[self.i] + x
