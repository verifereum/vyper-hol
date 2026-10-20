# struct literal as log arg
struct S:
    p: uint256
    q: bool

event E:
    a: S

@external
def f(x: uint256):
    log E(a=S(p=x, q=True))
