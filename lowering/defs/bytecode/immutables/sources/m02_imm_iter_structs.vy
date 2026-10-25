struct P:
    a: uint256
    b: uint256

A: immutable(P[2])

@deploy
def __init__():
    A = [P(a=1, b=2), P(a=3, b=4)]

@external
def f() -> uint256:
    s: uint256 = 0
    for p: P in A:
        s += p.b
    return s
