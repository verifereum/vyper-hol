@external
@pure
def f(y: Bytes[50]) -> Bytes[100]:
    c: Bytes[100] = concat(y, b"x")
    return c
