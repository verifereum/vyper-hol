m: HashMap[uint256, uint256]

@external
def f() -> uint256:
    d: DynArray[uint256, 3] = [5]
    self.m[d.pop()] = d[0]
    return self.m[5]
