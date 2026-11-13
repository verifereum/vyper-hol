A: immutable(uint256[2][2])

@deploy
def __init__():
    A = [[1, 2], [3, 4]]

@external
def get(i: uint256) -> uint256:
    return A[i][1]
