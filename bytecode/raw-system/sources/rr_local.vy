# @raw_return returning a memory local built by concat
@external
@raw_return
def f(a: Bytes[10]) -> Bytes[40]:
    b: Bytes[40] = concat(a, a)
    return b
