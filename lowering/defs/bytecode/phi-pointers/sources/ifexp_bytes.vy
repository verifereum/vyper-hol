# a10: ternary of Bytes type with literal branch
@external
def f(c: bool, a: Bytes[10]) -> Bytes[10]:
    return a if c else b"xy"
