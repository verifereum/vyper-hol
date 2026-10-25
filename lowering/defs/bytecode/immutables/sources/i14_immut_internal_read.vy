# a01: immutable read in an internal function called from external
X: immutable(uint256)

@deploy
def __init__():
    X = 3

@internal
def _g() -> uint256:
    return X * 2

@external
def f() -> uint256:
    return self._g()
