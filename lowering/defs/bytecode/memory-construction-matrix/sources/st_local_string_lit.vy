# struct local with String field from literal
struct S:
    s: String[10]
    a: uint256

@external
@pure
def f(a: uint256) -> S:
    x: S = S(s="hello", a=a)
    return x
