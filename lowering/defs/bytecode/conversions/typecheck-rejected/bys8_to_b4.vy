@external
@pure
def f(x: Bytes[8]) -> bytes4:
    return convert(x, bytes4)
