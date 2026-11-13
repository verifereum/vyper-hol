@external
@pure
def f(x: bytes4) -> Bytes[2]:
    return convert(x, Bytes[2])
