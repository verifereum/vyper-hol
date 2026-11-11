# raw_call with dynamic Bytes argument data and value
@external
@payable
def foo(t: address, d: Bytes[100]) -> Bytes[100]:
    return raw_call(t, d, max_outsize=100, value=msg.value)
