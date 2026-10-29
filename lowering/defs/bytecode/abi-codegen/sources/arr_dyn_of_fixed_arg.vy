# dynamic array of uint256[2] as argument only (decode path)
@external
@pure
def f(x: DynArray[uint256[2], 3]) -> uint256:
    return len(x)
