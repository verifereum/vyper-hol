# raw_call as statement, no max_outsize, literal bytes data
@external
def foo(t: address):
    raw_call(t, b"\x01\x02")
