# raw_call nested inside len()
@external
def foo(t: address) -> uint256:
    return len(raw_call(t, b"", max_outsize=32))
