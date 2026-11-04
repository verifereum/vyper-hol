# raw_call revert_on_failure=False with max_outsize -> (bool, Bytes)
@external
def foo(t: address) -> Bytes[32]:
    ok: bool = False
    res: Bytes[32] = b""
    ok, res = raw_call(t, b"", max_outsize=32, revert_on_failure=False)
    assert ok
    return res
