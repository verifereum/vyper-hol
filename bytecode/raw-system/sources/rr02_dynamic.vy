# raw_revert with dynamic data argument
@external
def foo(d: Bytes[100]):
    raw_revert(d)
