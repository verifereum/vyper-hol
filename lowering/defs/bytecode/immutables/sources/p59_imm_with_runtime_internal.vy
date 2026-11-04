X: immutable(uint256)
y: uint256

@internal
def _inc():
    self.y += X

@deploy
def __init__():
    X = 3

@external
def bump():
    self._inc()

@external
def get() -> uint256:
    return self.y
