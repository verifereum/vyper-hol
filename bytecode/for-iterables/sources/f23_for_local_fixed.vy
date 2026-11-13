@external
def f(a: uint256) -> uint256:
    xs: uint256[3] = [a, 2, 3]
    t: uint256 = 0
    for x: uint256 in xs:
        t += x
    return t
