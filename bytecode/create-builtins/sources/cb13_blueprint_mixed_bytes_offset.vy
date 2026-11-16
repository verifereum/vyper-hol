# Mixed literal classes keep the selector and enclosing length at runtime.
@external
def foo(t: address) -> address:
    return create_from_blueprint(t, code_offset=len([b"a", x"61"][0]))
