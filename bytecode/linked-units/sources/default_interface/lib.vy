x: public(uint256)


@external
def __default__():
    self.x = 7


@external
def f() -> uint256:
    return self.x + 1
