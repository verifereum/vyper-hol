# pop on an inner dynarray of a local nested dynarray
@external
def f(x: uint256) -> uint256:
    a: DynArray[DynArray[uint256, 3], 2] = [[1, 2], [x, 4, 5]]
    return a[1].pop()
