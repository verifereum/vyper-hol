X: immutable(bool)

@deploy
def __init__():
    X = True

@external
def f() -> bool:
    return X
