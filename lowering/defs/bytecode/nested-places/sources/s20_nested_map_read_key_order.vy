m: HashMap[uint256, HashMap[uint256, uint256]]
c: uint256

@internal
def g() -> uint256:
    self.c += 1
    return self.c

@internal
def h() -> uint256:
    self.c += 10
    return self.c

@external
def f() -> uint256:
    self.m[1][11] = 5
    self.c = 0
    return self.m[self.g()][self.h()]
