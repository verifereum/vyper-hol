# pragma enable-decimals
@external
@pure
def f(x: Bytes[16]) -> decimal:
    return convert(x, decimal)
