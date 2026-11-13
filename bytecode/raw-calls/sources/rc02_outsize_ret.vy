# raw_call with max_outsize, returned Bytes
@external
def foo(t: address) -> Bytes[32]:
    return raw_call(t, b"", max_outsize=32)
