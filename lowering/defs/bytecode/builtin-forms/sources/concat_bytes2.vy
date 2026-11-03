# concat of two Bytes args
@external
@pure
def f(a: Bytes[10], b: Bytes[20]) -> Bytes[30]:
    return concat(a, b)
