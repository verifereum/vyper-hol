# Unsafe arithmetic is evaluated at runtime even with constant operands.
@external
def foo(t: address) -> address:
    return create_from_blueprint(t, code_offset=unsafe_add(max_value(uint256), 0))
