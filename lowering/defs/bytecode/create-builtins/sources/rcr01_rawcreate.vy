# raw_create with bytecode only
@external
def foo(b: Bytes[100]) -> address:
    return raw_create(b)
