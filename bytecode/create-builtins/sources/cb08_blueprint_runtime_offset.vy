# Runtime blueprint offset without constructor encoding.
@external
def foo(t: address, o: uint256) -> address:
    return create_from_blueprint(t, code_offset=o)
