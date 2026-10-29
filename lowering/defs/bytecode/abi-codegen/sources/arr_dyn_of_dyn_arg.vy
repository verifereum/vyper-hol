# dynamic array of dynamic arrays as argument only (decode path)
@external
@pure
def f(x: DynArray[DynArray[uint256, 2], 2]) -> uint256:
    return len(x)
