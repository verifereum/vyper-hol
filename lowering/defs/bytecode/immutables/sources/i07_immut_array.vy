A: immutable(uint256[2])

@deploy
def __init__():
    A = [3, 4]

@external
def f() -> uint256:
    return A[0] + A[1]
