# a constructor local that stays live across an internal call, whose own
# locals need memory too
x: uint256

@internal
def bump(y: uint256) -> uint256:
    z: uint256 = y * 2
    return z + 1

@deploy
def __init__():
    a: uint256 = 7
    b: uint256 = self.bump(a)
    self.x = a + b

@external
def get() -> uint256:
    return self.x
