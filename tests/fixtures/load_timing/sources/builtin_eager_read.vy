c: uint256

@internal
def inc() -> uint256:
    self.c += 10
    return 1

@external
def f() -> uint256:
    self.c = 0
    return min(self.c, self.inc())
