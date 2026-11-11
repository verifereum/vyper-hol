# raw_call forwarding msg.data, revert_on_failure=False -> bool
@external
def foo(t: address) -> bool:
    return raw_call(t, msg.data, revert_on_failure=False)
