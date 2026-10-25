# internal fn used only at runtime while a Call-free __init__ exists
x: uint256

@internal
def _inc():
    self.x += 1

@deploy
def __init__():
    self.x = 5

@external
def bump():
    self._inc()

@external
def get() -> uint256:
    return self.x
