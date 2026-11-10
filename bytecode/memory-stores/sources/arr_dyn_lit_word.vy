@external
@pure
def f(a: uint256) -> DynArray[uint256, 3]:
    x: DynArray[uint256, 3] = [a, 1]
    return x
