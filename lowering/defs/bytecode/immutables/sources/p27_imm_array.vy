A: immutable(uint256[2])

@deploy
def __init__():
    A = [1, 2]

@external
def get() -> uint256[2]:
    return A

@external
def at() -> uint256:
    return A[1]
