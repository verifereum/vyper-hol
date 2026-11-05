arr: uint256[3]

@external
def set(x: uint256):
    self.arr = [x, 2, 1]

@external
def f() -> uint256:
    t: uint256 = 0
    for x: uint256 in self.arr:
        t += x
    return t
