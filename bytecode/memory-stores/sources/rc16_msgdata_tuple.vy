# raw_call forwarding msg.data, rof=False + max_outsize tuple
@external
def foo(t: address) -> Bytes[32]:
    ok: bool = False
    res: Bytes[32] = b""
    ok, res = raw_call(t, msg.data, max_outsize=32, revert_on_failure=False)
    return res
