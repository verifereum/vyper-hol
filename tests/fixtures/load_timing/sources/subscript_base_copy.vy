a: DynArray[uint256[2], 2]

@internal
def bar() -> uint256:
    self.a[0][1] = 9
    return 1

@external
def f() -> uint256:
    self.a = [[0, 5]]
    return self.a[0][self.bar()]
