X: immutable(uint256)

@deploy
def __init__():
    X = 42

@external
def get() -> uint256:
    return X
