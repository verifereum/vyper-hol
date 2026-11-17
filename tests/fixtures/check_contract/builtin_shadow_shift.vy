# An internal function named like a builtin: the bare call is the builtin.
counter: public(uint256)

@internal
def shift(x: uint256, n: int128) -> uint256:
    self.counter += 1
    return 42

@external
def f(x: uint256, n: int128) -> uint256:
    return shift(x, n)
