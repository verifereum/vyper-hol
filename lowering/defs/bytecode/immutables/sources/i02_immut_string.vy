S: immutable(String[10])

@deploy
def __init__():
    S = "hello"

@external
def f() -> String[10]:
    return S
