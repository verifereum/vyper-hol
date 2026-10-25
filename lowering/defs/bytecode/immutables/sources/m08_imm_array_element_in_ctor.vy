A: immutable(uint256[2])
n: uint256

@deploy
def __init__():
    A = [1, 2]
    self.n = A[1]

@external
def get() -> uint256:
    return self.n
