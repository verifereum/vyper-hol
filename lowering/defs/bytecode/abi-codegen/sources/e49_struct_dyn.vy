# struct with dynamic member as event field
struct S:
    p: uint256
    s: String[5]

event E:
    a: S

@external
def f(x: S):
    log E(a=x)
