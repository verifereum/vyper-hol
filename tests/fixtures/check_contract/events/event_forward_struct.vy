struct Outer:
    inner: Inner

struct Inner:
    x: uint256

event E:
    a: Outer

@external
def f(x: Outer):
    log E(a=x)
