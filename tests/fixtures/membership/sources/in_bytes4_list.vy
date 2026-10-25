# a10: bytes4 in literal list (needle from msg.data slice style)
@external
def f(x: bytes4) -> bool:
    return x in [0x01020304, 0xaabbccdd]
