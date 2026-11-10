# create_minimal_proxy_to basic
@external
def foo(t: address) -> address:
    return create_minimal_proxy_to(t)
