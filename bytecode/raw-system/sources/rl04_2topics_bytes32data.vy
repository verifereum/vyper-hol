# raw_log with 2 topics and bytes32 data
@external
def foo(a: bytes32, b: bytes32):
    raw_log([a, b], b)
