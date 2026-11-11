@external
def f(xs: DynArray[uint256, 4]) -> uint256:
    t: uint256 = 0
    for x: uint256 in xs:
        t += x
    return t
