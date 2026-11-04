# raw_call with data built by concat
@external
def foo(t: address, x: bytes32):
    raw_call(t, concat(b"\x12\x34\x56\x78", x))
