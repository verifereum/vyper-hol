d: DynArray[uint256, 3]

@internal
def shrink() -> uint256:
    return self.d.pop()

@external
def f():
    self.d[0] += self.shrink()
