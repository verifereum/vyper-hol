event E:
    a: DynArray[uint256, 5][2]

@external
def f(x: DynArray[uint256, 3][2]):
    log E(x)
