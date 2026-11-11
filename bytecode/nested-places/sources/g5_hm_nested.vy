m: HashMap[address, HashMap[address, uint256]]

@external
def f(a: address, b: address, x: uint256) -> uint256:
    self.m[a][b] = x
    return self.m[a][b]
