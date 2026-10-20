
@external
def create_and_destroy() -> address:
    child: address = raw_create(
        b"\x60\x04\x60\x0c\x60\x00\x39\x60\x04\x60\x00\xf3\x61\x01\x23\xff",
        value=10,
    )
    raw_call(child, b"")
    return child
