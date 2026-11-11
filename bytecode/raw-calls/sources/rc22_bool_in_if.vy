# raw_call revert_on_failure=False used as if condition (nested position)
@external
def foo(t: address) -> uint256:
    if raw_call(t, b"", revert_on_failure=False):
        return 1
    return 0
