# a11: assign a DynArray calldata argument to a DynArray local
@external
def f(xs: DynArray[uint256, 4]) -> uint256:
    d: DynArray[uint256, 4] = []
    d = xs
    return len(d)
