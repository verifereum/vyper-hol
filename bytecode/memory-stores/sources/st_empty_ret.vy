struct S:
    s: String[10]
    a: uint256
@external
@pure
def f() -> S:
    return empty(S)
