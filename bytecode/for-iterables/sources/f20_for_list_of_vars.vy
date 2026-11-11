@external
def f(a: uint256, b: uint256) -> uint256:
    t: uint256 = 0
    for x: uint256 in [a, b, a]:
        t += x
    return t
