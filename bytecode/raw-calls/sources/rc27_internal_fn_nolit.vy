# raw_call with outsize inside an internal function (argument data)
@internal
def h(t: address, d: Bytes[8]) -> Bytes[32]:
    return raw_call(t, d, max_outsize=32)
@external
def foo(t: address, d: Bytes[8]) -> Bytes[32]:
    return self.h(t, d)
