@external
@pure
def f(x: String[32]) -> Bytes[32]:
    return convert(x, Bytes[32])
