# create_from_blueprint with runtime code_offset and Bytes ctor arg
@external
def foo(t: address, o: uint256, d: Bytes[40]) -> address:
    return create_from_blueprint(t, d, code_offset=o)
