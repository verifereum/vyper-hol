# control (not a04): plain Bytes literal return without raw_return
@external
def f() -> Bytes[64]:
    return b"\x01\x02\x03"
