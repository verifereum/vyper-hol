# raw_call forwarding msg.data, is_static_call with outsize, view
@external
@view
def foo(t: address) -> Bytes[32]:
    return raw_call(t, msg.data, max_outsize=32, is_static_call=True)
