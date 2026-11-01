struct S:
    a: uint256
    b: uint256

m: HashMap[uint256, S]

@external
def f(k: uint256, x: uint256):
    self.m[k].b = x
