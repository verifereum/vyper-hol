# base for checker-domain mutations (not a probe itself)
event E1:
    a: uint256

event E2:
    a: uint256

x: uint256

@internal
@nonreentrant
def g(a: uint256):
    self.x = a

@external
def f(a: uint256):
    self.g(a)

@external
def burn(a: uint256):
    log E1(a=a)

@external
def cps(a: bytes16):
    log E2(a=1)

@external
@pure
def p(a: uint256) -> uint256:
    return a

@external
def __default__():
    pass

@deploy
def __init__():
    self.x = 1

@internal
def h() -> Bytes[10]:
    return b"ab"

@external
def k() -> Bytes[10]:
    return self.h()
