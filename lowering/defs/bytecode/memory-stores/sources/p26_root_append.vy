items: DynArray[uint256, 4]

@external
def f(v: uint256) -> DynArray[uint256, 3]:
    a: DynArray[uint256, 3] = [1]
    a.append(v)
    self.items.append(v)
    return a
