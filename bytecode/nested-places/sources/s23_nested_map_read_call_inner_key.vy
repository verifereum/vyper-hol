# a11: checker-eval control: nested map read with an internal call as the INNER key, x: uint256 = self.m[self.g()][1]
m: HashMap[uint256, HashMap[uint256, uint256]]
c: uint256

@internal
def g() -> uint256:
    self.c += 1
    return self.c

@external
def f() -> uint256:
    x: uint256 = self.m[self.g()][1]
    return x
