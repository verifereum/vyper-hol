m: HashMap[uint256, DynArray[uint256, 2]]

@external
def f(flag: bool) -> uint256:
    d: DynArray[uint256, 2] = [5, 0]
    self.m[d.pop()] = d if flag else d
    return len(self.m[0])
