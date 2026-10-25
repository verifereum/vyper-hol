# a01: struct immutable; field read at runtime
struct S:
    a: uint256
    b: address

V: immutable(S)

@deploy
def __init__():
    V = S(a=9, b=msg.sender)

@external
def f() -> address:
    return V.b
