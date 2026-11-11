struct S:
    a: uint256
    xs: uint256[2]

@external
@pure
def f(x: S) -> S:
    return x
