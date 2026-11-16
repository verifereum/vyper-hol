# Folded blueprint offset follows the literal code-size check.
@external
def foo(t: address) -> address:
    return create_from_blueprint(t, code_offset=1 + 2)
