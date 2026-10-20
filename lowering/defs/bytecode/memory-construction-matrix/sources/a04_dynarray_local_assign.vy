# a11: assign a list literal to a DynArray local after declaration
@external
def f() -> uint256:
    d: DynArray[uint256, 4] = [1]
    d = [7, 8]
    return d[1]
