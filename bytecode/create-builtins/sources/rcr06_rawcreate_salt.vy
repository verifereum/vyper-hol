# raw_create with salt, no ctor args
@external
def foo(b: Bytes[100], s: bytes32) -> address:
    return raw_create(b, salt=s)
