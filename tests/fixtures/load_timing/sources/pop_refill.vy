d: DynArray[uint256, 3]
m: HashMap[uint256, uint256]

@internal
def refill() -> uint256:
    self.d.append(9)
    return 0

@external
def f() -> uint256:
    self.d = [5]
    self.m[self.refill()] = self.d.pop()
    return self.m[0]
