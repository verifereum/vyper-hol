X: immutable(uint256)
y: uint256

@deploy
def __init__():
    X = 42
    self.y = X + 1

@external
def get() -> uint256:
    return X + self.y
