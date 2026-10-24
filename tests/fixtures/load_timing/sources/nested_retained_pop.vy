@external
def f() -> uint256:
    d: DynArray[DynArray[DynArray[uint256, 2], 2], 2] = [[[0, 5]]]
    return d[0][d.pop()[0][0]].pop()
