@external
def f(xs: uint256[3]) -> uint256:
    t: uint256 = 0
    for x: uint256 in xs:
        t += x
    return t
