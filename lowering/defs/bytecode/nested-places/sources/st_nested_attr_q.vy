struct T:
    p: uint256
    q: uint256

struct S:
    a: uint256
    t: T

@external
@pure
def f(x: S) -> uint256:
    return x.t.q
