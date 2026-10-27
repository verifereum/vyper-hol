# a10: ternary of DynArray type
@external
def f(c: bool, a: DynArray[uint256, 3], b: DynArray[uint256, 3]) -> DynArray[uint256, 3]:
    return a if c else b
