# raw_call forwarding msg.data with max_outsize, returned
@external
def foo(t: address) -> Bytes[64]:
    return raw_call(t, msg.data, max_outsize=64)
