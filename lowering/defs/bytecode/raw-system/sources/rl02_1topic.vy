# raw_log with 1 topic and empty data
@external
def foo(a: bytes32):
    raw_log([a], b"")
