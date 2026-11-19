import lib

initializes: lib

exports: lib.get_x

x: uint256
OWN: immutable(uint256)


@deploy
def __init__():
    OWN = 7
    lib.__init__(5)
    self.x = 2


@internal
def foo() -> uint256:
    return self.x + OWN


@external
def bar() -> uint256:
    return self.foo() + lib.foo()
