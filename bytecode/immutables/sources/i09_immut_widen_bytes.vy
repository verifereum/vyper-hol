X: immutable(Bytes[100])

@deploy
def __init__(x: String[10]):
    X = convert(x, Bytes[100])

@external
def get() -> Bytes[100]:
    return X
