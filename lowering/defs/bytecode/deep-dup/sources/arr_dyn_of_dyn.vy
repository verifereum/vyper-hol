# dynamic array of dynamic arrays as argument and return
@external
@pure
def f(x: DynArray[DynArray[uint256, 2], 2]) -> DynArray[DynArray[uint256, 2], 2]:
    return x
