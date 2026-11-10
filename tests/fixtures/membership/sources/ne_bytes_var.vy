# a10: != on Bytes args
@external
def f(a: Bytes[40], b: Bytes[40]) -> bool:
    return a != b
