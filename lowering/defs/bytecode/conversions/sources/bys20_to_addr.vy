@external
@pure
def f(x: Bytes[20]) -> address:
    return convert(x, address)
