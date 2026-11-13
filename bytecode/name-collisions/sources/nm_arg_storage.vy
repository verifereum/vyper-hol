# external argument named like a storage variable: `stored` is the argument,
# `self.stored` is storage slot 0 (#557, a04-03)
stored: uint256

@external
def f(stored: uint256) -> uint256:
    self.stored = stored + 1
    return self.stored + stored
