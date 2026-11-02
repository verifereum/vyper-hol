# raw_call with is_delegate_call=True and max_outsize, returned Bytes
@external
def foo(t: address, x: Bytes[64]) -> Bytes[32]:
    return raw_call(t, x, max_outsize=32, is_delegate_call=True)
