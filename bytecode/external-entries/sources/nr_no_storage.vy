# nonreentrant on a function that writes no storage
@external
@nonreentrant
def f(a: uint256) -> uint256:
    return a + 1
