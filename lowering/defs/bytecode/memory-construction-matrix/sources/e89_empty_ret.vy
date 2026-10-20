# control (cross-area): empty(uint256[2]) returned after memory was dirtied (no log)
@external
def f(x: uint256) -> uint256[2]:
    a: uint256[2] = [x, x]
    return empty(uint256[2])
