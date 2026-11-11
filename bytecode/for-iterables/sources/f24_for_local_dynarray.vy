@external
def f(a: uint256) -> uint256:
    xs: DynArray[uint256, 4] = [a, 2]
    t: uint256 = 0
    for x: uint256 in xs:
        t += x
    return t
