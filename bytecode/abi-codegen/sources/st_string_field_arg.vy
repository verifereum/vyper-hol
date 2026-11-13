# struct with a String field as argument only (decode path, getelemptr no-wrap guard)
struct S:
    a: uint256
    s: String[10]

@external
@pure
def f(x: S) -> uint256:
    return x.a
