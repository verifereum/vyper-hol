d: DynArray[uint256, 3]
m: HashMap[uint256, DynArray[uint256, 3]]

@internal
def change() -> uint256:
    self.d[0] = 9
    return 0

@external
def f(flag: bool) -> uint256:
    self.d = [5]
    self.m[self.change()] = self.d if flag else self.d
    return self.m[0][0]
