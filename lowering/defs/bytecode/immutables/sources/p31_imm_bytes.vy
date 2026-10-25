B: immutable(Bytes[64])

@deploy
def __init__():
    B = b"abcdefghijklmnopqrstuvwxyz0123456789"

@external
def get() -> Bytes[64]:
    return B
