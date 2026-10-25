B: immutable(bytes20)

@deploy
def __init__():
    B = 0x0102030405060708091011121314151617181920

@external
def get() -> bytes20:
    return B
