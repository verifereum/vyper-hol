X: immutable(address)

@deploy
def __init__():
    X = msg.sender

@external
def get() -> address:
    return X
