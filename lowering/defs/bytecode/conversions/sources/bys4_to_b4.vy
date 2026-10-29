@external
@pure
def f(x: Bytes[4]) -> bytes4:
    return convert(x, bytes4)
