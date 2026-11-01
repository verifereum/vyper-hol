X: immutable(uint8)

@deploy
def __init__(x: uint8):
    X = x

@external
def get() -> uint8:
    return X
