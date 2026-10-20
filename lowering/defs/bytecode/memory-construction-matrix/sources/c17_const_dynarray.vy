# a01: constant DynArray-typed value assigned to a local
A: constant(DynArray[uint256, 3]) = [1, 2]

@external
def f() -> DynArray[uint256, 3]:
    a: DynArray[uint256, 3] = A
    return a
