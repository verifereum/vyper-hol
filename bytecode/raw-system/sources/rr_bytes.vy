# @raw_return returning Bytes
@external
@raw_return
def f() -> Bytes[64]:
    return b"\x01\x02\x03"
