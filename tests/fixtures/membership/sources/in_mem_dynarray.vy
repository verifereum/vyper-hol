# a10-03: dynamic bound assertion belongs in in_entry.
@external
def f(x: uint256, a: DynArray[uint256, 4]) -> bool:
    return x in a
