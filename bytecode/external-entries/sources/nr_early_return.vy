# nonreentrant with an early return inside a branch (unlock on each exit)
@external
@nonreentrant
def f(a: uint256) -> uint256:
    if a > 5:
        return 1
    return 2
