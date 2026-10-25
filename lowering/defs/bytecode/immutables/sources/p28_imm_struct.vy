# struct immutable
struct P:
    a: uint256
    b: uint256

Q: immutable(P)

@deploy
def __init__():
    Q = P(a=5, b=6)

@external
def get() -> uint256:
    return Q.b
