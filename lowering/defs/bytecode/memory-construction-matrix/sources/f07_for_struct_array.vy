# a11: for over a local fixed array of structs
struct S:
    a: uint256
    b: uint256

@external
def f(z: uint256) -> uint256:
    xs: S[2] = [S(a=z, b=2), S(a=3, b=4)]
    t: uint256 = 0
    for s: S in xs:
        t += s.b
    return t
