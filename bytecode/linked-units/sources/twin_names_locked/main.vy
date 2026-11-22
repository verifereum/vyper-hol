import lib

initializes: lib

exports: (lib.get_x, lib.locked_get_x)

x: uint256
IMM: immutable(uint256)


@deploy
def __init__():
    IMM = 7
    lib.__init__(5)
    self.x = 2


@internal
def foo() -> uint256:
    return self.x + IMM


@external
def bar() -> uint256:
    return self.foo() + lib.foo()
