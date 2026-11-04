# raw_call (no outsize) inside an internal function, internal returns uint256
@internal
def h(t: address, d: Bytes[8]) -> uint256:
    raw_call(t, d)
    return 1
@external
def foo(t: address, d: Bytes[8]) -> uint256:
    return self.h(t, d)
