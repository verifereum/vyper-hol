# nested HashMap aug-assign (allowance pattern)
m: HashMap[address, HashMap[address, uint256]]

@external
def f(a: address, b: address, x: uint256):
    self.m[a][b] -= x
