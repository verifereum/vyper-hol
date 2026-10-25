S: immutable(String[40])
n: uint256

@deploy
def __init__():
    S = "abc"
    t: String[40] = S
    self.n = len(t)

@external
def get() -> uint256:
    return self.n
