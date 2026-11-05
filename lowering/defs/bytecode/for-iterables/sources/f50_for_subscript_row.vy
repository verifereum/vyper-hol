@external
def f(a: uint256) -> uint256:
    rows: uint256[2][2] = [[a, 2], [3, 4]]
    t: uint256 = 0
    for x: uint256 in rows[0]:
        t += x
    return t
