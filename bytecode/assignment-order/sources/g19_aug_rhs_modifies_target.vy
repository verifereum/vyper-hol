c: uint256

@internal
def inc() -> uint256:
    self.c += 10
    return 1

@external
def f():
    self.c += self.inc()
