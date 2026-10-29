c: uint256

@internal
def inc() -> uint256:
    self.c += 10
    return 1

@internal
def first(a: uint256, b: uint256) -> uint256:
    return a

@external
def f() -> uint256:
    self.c = 0
    return self.first(self.c, self.inc())
