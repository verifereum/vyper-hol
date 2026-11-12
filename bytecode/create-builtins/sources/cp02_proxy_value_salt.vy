# create_minimal_proxy_to with value and salt
@external
@payable
def foo(t: address, s: bytes32) -> address:
    return create_minimal_proxy_to(t, value=msg.value, salt=s)
