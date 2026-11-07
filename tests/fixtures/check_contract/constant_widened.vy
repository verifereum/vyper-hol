B: constant(Bytes[5]) = b"abc"
A: constant(Bytes[10]) = B


@external
@pure
def g(x: Bytes[10]) -> bool:
    return x == A
