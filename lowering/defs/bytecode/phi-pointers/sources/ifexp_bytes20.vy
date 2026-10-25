# a10: ternary of bytes20 type
@external
def f(c: bool, a: bytes20, b: bytes20) -> bytes20:
    return a if c else b
