# raw_call is_static_call=True with max_outsize, in a view function
@external
@view
def foo(t: address) -> Bytes[64]:
    return raw_call(t, b"\xaa", max_outsize=64, is_static_call=True)
