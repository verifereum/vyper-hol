@internal
def n() -> DynArray[DynArray[uint256, 2], 2]:
    return [[1, 2], [3, 4]]

@external
def f(c: bool, b: DynArray[DynArray[uint256, 5], 2]) -> DynArray[DynArray[uint256, 5], 2]:
    return self.n() if c else b
