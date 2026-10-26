# DynArray of struct event field
struct S:
    p: uint256
    q: uint256

event E:
    a: DynArray[S, 2]

@external
def f(x: DynArray[S, 2]):
    log E(a=x)
