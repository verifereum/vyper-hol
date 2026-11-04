# raw_call revert_on_failure=False, max_outsize=0 -> bool
@external
def foo(t: address) -> bool:
    return raw_call(t, b"", revert_on_failure=False)
