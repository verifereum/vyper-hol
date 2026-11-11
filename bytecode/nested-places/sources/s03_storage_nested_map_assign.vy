m: HashMap[address, HashMap[uint256, uint256]]

@external
def f(a: address, b: uint256, x: uint256):
    self.m[a][b] = x
