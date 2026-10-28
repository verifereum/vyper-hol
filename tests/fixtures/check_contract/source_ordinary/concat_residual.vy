@external
@pure
def f(a: Bytes[4], b: Bytes[4]) -> Bytes[8]:
    return concat(a, b)
