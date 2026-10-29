# struct with a String field as argument and return
struct S:
    a: uint256
    s: String[10]

@external
@pure
def f(x: S) -> S:
    return x
