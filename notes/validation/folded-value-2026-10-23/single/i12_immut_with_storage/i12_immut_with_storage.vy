N: constant(uint256) = 10
X: immutable(uint256)
s: uint256

@deploy
def __init__():
    X = N * 2
    self.s = 1

@external
def f() -> uint256:
    return X + self.s + N
