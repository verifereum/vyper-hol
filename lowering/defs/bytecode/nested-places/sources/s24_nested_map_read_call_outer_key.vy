# a11: checker-eval control: nested map read with an internal call as the OUTER key only, x: uint256 = self.m[1][self.g()]
m: HashMap[uint256, HashMap[uint256, uint256]]
c: uint256

@internal
def g() -> uint256:
    self.c += 1
    return self.c

@external
def f() -> uint256:
    x: uint256 = self.m[1][self.g()]
    return x
