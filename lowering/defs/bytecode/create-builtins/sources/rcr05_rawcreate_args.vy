# raw_create with ctor args, no salt
@external
def foo(b: Bytes[100], x: uint256) -> address:
    return raw_create(b, x)
