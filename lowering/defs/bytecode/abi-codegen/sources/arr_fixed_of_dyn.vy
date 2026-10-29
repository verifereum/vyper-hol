# fixed array of dynamic arrays as argument and return
@external
@pure
def f(x: DynArray[uint256, 3][2]) -> DynArray[uint256, 3][2]:
    return x
