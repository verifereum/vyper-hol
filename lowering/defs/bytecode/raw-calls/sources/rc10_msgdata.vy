# raw_call forwarding msg.data (calldata form), statement
@external
def foo(t: address):
    raw_call(t, msg.data)
