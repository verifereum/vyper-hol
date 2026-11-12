# constructor locals next to a constructor argument
x: uint256

@deploy
def __init__(a: uint256):
    c: uint256[2] = [a, a + 1]
    self.x = c[0] + c[1]

@external
def get() -> uint256:
    return self.x
