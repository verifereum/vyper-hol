# struct with word fields as argument and return (supported baseline)
struct S:
    a: uint256
    b: address

@external
@pure
def f(x: S) -> S:
    return x
