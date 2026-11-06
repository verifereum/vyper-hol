# create_copy_of with salt and value
@external
@payable
def foo(t: address, s: bytes32) -> address:
    return create_copy_of(t, value=msg.value, salt=s)
