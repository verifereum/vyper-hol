@external
@pure
def f(a: uint256) -> DynArray[uint256, 3]:
    y: DynArray[uint256, 3] = [a, a]
    x: DynArray[uint256, 3] = empty(DynArray[uint256, 3])
    return x
