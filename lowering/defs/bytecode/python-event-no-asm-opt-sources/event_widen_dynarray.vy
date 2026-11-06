event E:
    a: DynArray[uint256, 5]

@external
def f(x: DynArray[uint256, 3]):
    log E(x)
