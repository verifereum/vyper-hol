@external
def foo(t: address) -> address:
    return create_from_blueprint(t, code_offset=len([b"a", b"ab"][0]))
