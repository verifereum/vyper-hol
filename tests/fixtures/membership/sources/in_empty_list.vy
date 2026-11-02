# a10: membership in empty literal list (if allowed)
@external
def f(x: uint256) -> bool:
    return x in empty(DynArray[uint256, 3])
