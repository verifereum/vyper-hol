# a17: runtime for-loop over a word-element immutable array (uint256[3])
A: immutable(uint256[3])

@deploy
def __init__():
    A = [1, 2, 3]

@external
def f() -> uint256:
    s: uint256 = 0
    for x: uint256 in A:
        s += x
    return s
