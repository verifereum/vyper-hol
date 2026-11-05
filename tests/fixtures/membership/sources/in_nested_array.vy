# a10: DynArray in array of DynArrays (non-word element)
@external
def f(x: DynArray[uint256, 2], a: DynArray[DynArray[uint256, 2], 2]) -> bool:
    return x in a
