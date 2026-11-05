@external
def f() -> uint256:
    t: uint256 = 0
    for x: uint256 in [1, 2, 3]:
        t += x
    return t
