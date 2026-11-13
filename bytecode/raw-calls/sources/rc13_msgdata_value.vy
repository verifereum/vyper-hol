# raw_call forwarding msg.data with value=
@external
@payable
def foo(t: address):
    raw_call(t, msg.data, value=msg.value)
