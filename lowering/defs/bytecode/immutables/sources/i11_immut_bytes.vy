B: immutable(Bytes[32])

@deploy
def __init__():
    B = b"hello"

@external
def f() -> Bytes[32]:
    return B
