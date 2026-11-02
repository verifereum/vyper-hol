# create_minimal_proxy_to revert_on_failure=False
@external
def foo(t: address) -> address:
    return create_minimal_proxy_to(t, revert_on_failure=False)
