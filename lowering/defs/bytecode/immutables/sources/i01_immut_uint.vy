X: immutable(uint256)

@deploy
def __init__(x: uint256):
    X = x

@external
def f() -> uint256:
    return X
