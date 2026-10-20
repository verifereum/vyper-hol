# empty() of a word-field struct as a local
struct S:
    a: uint256
    b: bool

@external
@pure
def f() -> S:
    x: S = empty(S)
    return x
