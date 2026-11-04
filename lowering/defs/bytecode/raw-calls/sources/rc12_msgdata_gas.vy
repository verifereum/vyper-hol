# raw_call forwarding msg.data with gas= kwarg
@external
def foo(t: address, g: uint256):
    raw_call(t, msg.data, gas=g)
