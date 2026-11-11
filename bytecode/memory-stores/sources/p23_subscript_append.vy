@external
def f(i: uint256, v: uint256) -> DynArray[DynArray[uint256, 3], 2]:
    a: DynArray[DynArray[uint256, 3], 2] = [[1], [2]]
    a[i].append(v)
    return a
