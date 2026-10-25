# internal fn called from __init__ reads/writes immutable-dependent value (excluded by constructor_call_free)
X: immutable(uint256)
y: uint256

@internal
def _g() -> uint256:
    return X * 2

@deploy
def __init__():
    X = 9
    self.y = self._g()

@external
def get() -> uint256:
    return self.y
