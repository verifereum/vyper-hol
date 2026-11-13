# create_from_blueprint code_offset, salt, value
@external
@payable
def foo(t: address, s: bytes32) -> address:
    return create_from_blueprint(t, code_offset=0, salt=s, value=msg.value)
