S: immutable(String[40])

@deploy
def __init__():
    S = "hello"

@external
def get() -> String[40]:
    return S
