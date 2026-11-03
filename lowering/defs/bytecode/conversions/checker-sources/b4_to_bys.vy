@external
@pure
def f(x: bytes4) -> Bytes[4]:
    return convert(x, Bytes[4])
