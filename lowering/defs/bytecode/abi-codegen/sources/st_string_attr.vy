# attribute read of a String field of a calldata struct
struct S:
    a: uint256
    s: String[10]

@external
@pure
def f(x: S) -> String[10]:
    return x.s
