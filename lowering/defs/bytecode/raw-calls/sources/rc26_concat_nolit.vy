# raw_call with data built by concat of arguments (no bytes literal)
@external
def foo(t: address, x: bytes32, d: Bytes[4]):
    raw_call(t, concat(d, x))
