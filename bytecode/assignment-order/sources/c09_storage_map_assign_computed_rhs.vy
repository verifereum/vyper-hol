# a11: evaluate the computed RHS before the mapping key and hash.
m: HashMap[uint256, uint256]

@external
def f(k: uint256, x: uint256):
    self.m[k + 1] = x * 2
