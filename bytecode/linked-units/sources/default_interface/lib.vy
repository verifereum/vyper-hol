x: public(uint256)


@internal
def g():
    self.x = 7


@internal
def h() -> uint256:
    return self.x + 1


@external
def __default__():
    self.g()


@external
def f() -> uint256:
    return self.h()
