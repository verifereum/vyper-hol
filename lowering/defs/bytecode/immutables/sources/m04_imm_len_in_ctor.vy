S: immutable(String[40])
n: uint256

@deploy
def __init__():
    S = "abc"
    self.n = len(S)

@external
def get() -> uint256:
    return self.n
