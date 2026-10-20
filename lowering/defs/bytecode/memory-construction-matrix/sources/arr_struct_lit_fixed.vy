# fixed array literal of struct literals
struct S:
    a: uint256
    b: bool

@external
@pure
def f(a: uint256) -> S[2]:
    x: S[2] = [S(a=a, b=True), S(a=2, b=False)]
    return x
