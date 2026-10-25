# a10: != Bytes[2] arg with bytes literal of same length
@external
def f(a: Bytes[2]) -> bool:
    return a != b"\x01\x02"
