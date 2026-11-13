m: HashMap[uint256, DynArray[uint256, 3]]

@external
def f():
    d: DynArray[DynArray[uint256, 3], 3] = [[1, 2]]
    self.m[d[0].pop() + d.pop()[0]] = d[0]
