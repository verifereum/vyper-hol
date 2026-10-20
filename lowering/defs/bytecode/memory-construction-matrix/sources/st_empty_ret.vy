# empty() of a struct with String field
struct S:
    s: String[10]
    a: uint256

@external
@pure
def f() -> S:
    return empty(S)
