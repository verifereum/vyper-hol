# struct with a dynamic array field as argument and return
struct S:
    a: uint256
    xs: DynArray[uint256, 3]

@external
@pure
def f(x: S) -> S:
    return x
