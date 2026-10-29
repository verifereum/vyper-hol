struct S:
    a: uint256
    b: uint256

@external
@pure
def f(x: DynArray[S, 3], i: uint256) -> uint256:
    return x[i].b
