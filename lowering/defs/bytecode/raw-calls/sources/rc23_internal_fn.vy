# raw_call with outsize inside an internal function
@internal
def h(t: address) -> Bytes[32]:
    return raw_call(t, b"\x01", max_outsize=32)
@external
def foo(t: address) -> Bytes[32]:
    return self.h(t)
