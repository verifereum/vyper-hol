# create_minimal_proxy_to nested as argument to raw_call
@external
def foo(t: address):
    raw_call(create_minimal_proxy_to(t), b"")
