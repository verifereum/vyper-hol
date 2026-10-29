# event field of nested array DynArray[uint256[2], 2] (non-indexed)
event E:
    a: DynArray[uint256[2], 2]

@external
def f(x: DynArray[uint256[2], 2]):
    log E(a=x)
