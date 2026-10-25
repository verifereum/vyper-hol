B: immutable(Bytes[96])

@deploy
def __init__():
    B = b"abcdefghijklmnopqrstuvwxyz0123456789abcdefghijklmnopqrstuvwxyz0123456789"

@external
def get() -> Bytes[96]:
    return B
