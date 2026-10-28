c: uint256
m: HashMap[uint256, uint256]

@internal
def inc() -> uint256:
    self.c += 1
    return self.c

@external
def f():
    self.m[self.inc()] = self.c
