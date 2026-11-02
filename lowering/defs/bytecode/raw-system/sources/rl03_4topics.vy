# raw_log with 4 topics and dynamic data
@external
def foo(a: bytes32, b: bytes32, d: Bytes[64]):
    raw_log([a, b, a, b], d)
