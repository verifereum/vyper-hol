# a11: assign a storage struct to a local struct after declaration
struct S:
    a: uint256
    b: uint256

st: S

@external
def f() -> uint256:
    s: S = S(a=0, b=0)
    s = self.st
    return s.b
