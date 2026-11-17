# Source-aware comparison folding feeds the Boolean keyword argument.
@external
def foo(t: address) -> address:
    return create_from_blueprint(t, code_offset=0, revert_on_failure=True and (1 in [1, 2]))
