m: HashMap[uint256, DynArray[uint256, 3]]

@external
def f(k: uint256, x: uint256):
    self.m[k].append(1)
    self.m[k][0] = x
