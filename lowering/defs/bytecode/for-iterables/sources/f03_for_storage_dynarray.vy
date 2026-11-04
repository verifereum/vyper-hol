d: DynArray[uint256, 5]

@external
def set(x: uint256):
    self.d = [x, 2]

@external
def f() -> uint256:
    t: uint256 = 0
    for x: uint256 in self.d:
        t += x
    return t
