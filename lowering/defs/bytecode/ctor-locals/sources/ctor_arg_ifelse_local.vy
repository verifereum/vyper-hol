# a constructor local computed from an argument, read in both branches of an
# if/else
x: uint256

@deploy
def __init__(a: uint256):
    t: uint256 = a * 2
    if t > 10:
        self.x = t
    else:
        self.x = 10

@external
def get() -> uint256:
    return self.x
