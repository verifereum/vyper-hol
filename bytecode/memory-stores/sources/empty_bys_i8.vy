@external
def f() -> int8:
    a: Bytes[1] = b"\xff"
    a = b""
    return convert(a, int8)
