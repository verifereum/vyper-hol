# fixed array of dynamic arrays as argument only (decode path)
@external
@pure
def f(x: DynArray[uint256, 3][2]) -> uint256:
    return len(x[1])
