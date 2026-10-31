# dynamic array of fixed arrays as argument and return
@external
@pure
def f(x: DynArray[uint256[2], 3]) -> DynArray[uint256[2], 3]:
    return x
