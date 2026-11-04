# raw_call as statement with Bytes argument data (no literal)
@external
def foo(t: address, d: Bytes[64]):
    raw_call(t, d)
