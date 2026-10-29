# internal function taking/returning a struct with a String field
struct S:
    a: uint256
    s: String[10]

@internal
@pure
def g(x: S) -> S:
    return x

@external
@pure
def f(x: S) -> S:
    return self.g(x)
